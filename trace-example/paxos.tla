------------------------------- MODULE paxos -------------------------------
(***************************************************************************)
(* `^                                                                      *)
(*                                                                         *)
(* This is a specification of the paxos algorithm implemented in Ceph.     *)
(* The specification is based on the following source file:                *)
(* https://github.com/ceph/ceph/blob/master/src/mon/Paxos.cc \newline      *)
(*                                                                         *)
(* The main deviations/abstractions done that may differ from the          *)
(* implementation are:                                                     *)
(*                                                                         *)
(* \begin{itemize}                                                         *)
(*   \item \ The election logic. The leader is chosen randomly, and,       *)
(*   for now, only one leader is chosen per epoch.                         *)
(*                                                                         *)
(*   \item \ The quorum of monitors. For now, the specification considers  *)
(*   the quorum to be the set of all monitors and that the quorum does     *)
(*   not change over time.                                                 *)
(*                                                                         *)
(*   \item \ The communication layer. The variable messages holds the      *)
(*   messages waiting to be handled. For now, messages cannot be randomly  *)
(*   duplicated nor lost, and some messages can be received out of order.  *)
(*                                                                         *)
(*   \item \ The transactions. In this specification, transactions         *)
(*   represent only a change of value in the variable monitor\_store.      *)
(*                                                                         *)
(*   \item \ Failure model. For now, if a monitor crashes it will          *)
(*   instantly restart, resetting some variables and continuing to         *)
(*   participate in the quorum.                                            *)
(* \end{itemize}                                                           *)
(*                                                                         *)
(* For a more detailed overview of the specification:                      *)
(* https://github.com/afonsonf/ceph-consensus-spec                         *)
(*                                                                         *)
(* ^'                                                                      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC, SequencesExt, FiniteSetsExt

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Constants   }                                                *)
(*  ^'                                                                     *)
(***************************************************************************)

\* Set of monitors.
CONSTANTS Monitors

\* Sequence of monitors and the rank predicate, used to compute proposal numbers.
ranks == SetToSeq(Monitors)
rank(mon) == CHOOSE i \in 1..Len(ranks): ranks[i]=mon

\* Set of possible values.
CONSTANTS Value_set

\* Reserved value.
CONSTANTS Nil

\* Paxos states:
CONSTANTS STATE_RECOVERING,STATE_ACTIVE,
          STATE_UPDATING, STATE_UPDATING_PREVIOUS,
          STATE_WRITING, STATE_WRITING_PREVIOUS,
          STATE_REFRESH, STATE_SHUTDOWN

state_names == {STATE_RECOVERING, STATE_ACTIVE,
          STATE_UPDATING, STATE_UPDATING_PREVIOUS,
          STATE_WRITING, STATE_WRITING_PREVIOUS,
          STATE_REFRESH, STATE_SHUTDOWN}

\* Paxos auxiliary phase states:
\* They are used to force some sequence of steps.
CONSTANTS PHASE_ELECTION,
          PHASE_PRE_COLLECT, PHASE_COLLECT,
          PHASE_LEASE, PHASE_LEASE_DONE,
          PHASE_BEGIN, PHASE_BEGIN_DONE,
          PHASE_COMMIT, PHASE_COMMIT_DONE

phase_names == {PHASE_ELECTION,
          PHASE_PRE_COLLECT, PHASE_COLLECT,
          PHASE_LEASE, PHASE_LEASE_DONE,
          PHASE_BEGIN, PHASE_BEGIN_DONE,
          PHASE_COMMIT, PHASE_COMMIT_DONE}

\* Paxos message types:
CONSTANTS OP_COLLECT, OP_LAST,
          OP_BEGIN, OP_ACCEPT, OP_COMMIT,
          OP_LEASE, OP_LEASE_ACK

messages_types == {OP_COLLECT, OP_LAST,
          OP_BEGIN, OP_ACCEPT, OP_COMMIT,
          OP_LEASE, OP_LEASE_ACK}

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Global variables   }                                         *)
(* ^'                                                                      *)
(***************************************************************************)

\* Integer representing the current epoch. If is odd trigger an election.
\* Type: Integer
VARIABLE epoch

\* A function that stores messages.
\* Type: << message >>
VARIABLE messages

\* Stores history of message events. Can be useful to find specific states.
\* Type: { messages }
VARIABLE message_history

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   State variables   }                                          *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores the current leader. isLeader[mon] is True iff mon is a leader, else False.
\* Type: [Monitors |-> Bool]
VARIABLE isLeader

\* A function that stores the state of each monitor.
\* Type: [Monitors |-> state_names]
VARIABLE state

\* A function that stores the phase of each monitor.
\* Type: [Monitors |-> phase_names]
VARIABLE phase

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Restart variables   }                                        *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores, for each monitor, a value version when the commit phase starts.
\* This value version can be retrieved after a monitor crashes and restarts.
\* Type: [Monitors |-> value version]
VARIABLE uncommitted_v

\* A function that stores, for each monitor, a value when the commit phase starts.
\* This value can be retrieved after a monitor crashes and restarts.
\* Type: [Monitors |-> Value_set]
VARIABLE uncommitted_value

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Data variables   }                                           *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores, for each monitor, the current store where the transactions are applied.
\* In this model, a transaction represents changing the value in the store.
\* Type: [Monitors |-> Value_set]
VARIABLE monitor_store

\* A function that stores the transaction log of each monitor.
\* Type: [Monitors |-> [value version |-> Value_set]]
VARIABLE values

\* A function that stores the last proposal number accepted by each monitor.
\* Type: [Monitors |-> proposal number]
VARIABLE accepted_pn

\* A function that stores the first value version committed for each monitor.
\* Type: [Monitors |-> value version]
VARIABLE first_committed

\* A function that stores the last value version committed for each monitor.
\* Type: [Monitors |-> value version]
VARIABLE last_committed

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Collect phase variables   }                                  *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores the number of peers that accepted a collect request.
\* Type: [Monitors |-> number of peers that accepted]
VARIABLE num_last

\* Used by leader when receiving responses in collect phase.
\* Type: [Monitors |-> [Monitors |-> value version]]
VARIABLE peer_first_committed

\* Used by leader when receiving responses in collect phase.
\* Type: [Monitors |-> [Monitors |-> value version]]
VARIABLE peer_last_committed

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Lease phase variables   }                                    *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores, for each monitor, which of the peers have acked the lease request.
\* Type: [Monitors |-> [Monitors |-> Bool]]
VARIABLE acked_lease

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Commit phase variables   }                                   *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores, for each monitor, the value proposed by a client.
\* Type: [Monitors |-> Value_set \union {Nil}]
VARIABLE pending_proposal

\* A function that stores, for each monitor, the value to be committed in the begin phase.
\* Type: [Monitors |-> Value_set \union {Nil}]
VARIABLE new_value

\* A function that stores, for each monitor, which of the peers have acked the begin request.
\* Type: [Monitord |-> [Monitors |-> Bool]]
VARIABLE accepted

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Debug variables   }                                          *)
(* ^'                                                                      *)
(***************************************************************************)

\* Variables to help debug a behavior.
\* step is the diameter of a behavior/path.
\* step_x the current predicate being called.
VARIABLE step, step_x

\* Variables to limit the number of monitors crashes that can occur over a behavior.
\* This variable is used to limit the search space.
VARIABLE number_refreshes

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Variables initialization   }                                 *)
(* ^'                                                                      *)
(***************************************************************************)

global_vars    == <<epoch, messages, message_history>>
state_vars     == <<isLeader, state, phase>>
restart_vars   == <<uncommitted_v, uncommitted_value>>
data_vars      == <<monitor_store, values, accepted_pn, first_committed, last_committed>>
collect_vars   == <<num_last, peer_first_committed, peer_last_committed>>
lease_vars     == <<acked_lease>>
commit_vars    == <<pending_proposal, new_value, accepted>>

vars == <<global_vars, state_vars, restart_vars, data_vars, collect_vars,
          lease_vars, commit_vars>>

Init_global_vars ==
    /\ epoch = 1
    /\ messages = <<>>
    /\ message_history = {}

Init_state_vars ==
    /\ isLeader = [mon \in Monitors |-> FALSE]
    /\ state = [mon \in Monitors |-> Nil]
    /\ phase = [mon \in Monitors |-> Nil]

Init_restart_vars ==
    /\ uncommitted_v = [mon \in Monitors |-> 0]
    /\ uncommitted_value = [mon \in Monitors |-> Nil]

Init_data_vars ==
    /\ monitor_store = [mon \in Monitors |-> Nil]
    /\ values = [mon \in Monitors |-> [version \in {} |-> Nil]]
    /\ accepted_pn = [mon \in Monitors |-> 0]
    /\ first_committed = [mon \in Monitors |-> 0]
    /\ last_committed = [mon \in Monitors |-> 0]

Init_collect_vars ==
    /\ num_last = [mon \in Monitors |-> 0]
    /\ peer_first_committed = [mon1 \in Monitors |-> [mon2 \in Monitors |-> -1]]
    /\ peer_last_committed = [mon1 \in Monitors |-> [mon2 \in Monitors |-> -1]]

Init_lease_vars ==
    /\ acked_lease = [mon1 \in Monitors |-> [mon2 \in Monitors |-> FALSE]]

Init_commit_vars ==
    /\ pending_proposal = [mon \in Monitors |-> Nil]
    /\ new_value = [mon \in Monitors |-> Nil]
    /\ accepted = [mon1 \in Monitors |-> [mon2 \in Monitors |-> FALSE]]

Init ==
    /\ Init_global_vars
    /\ Init_state_vars
    /\ Init_restart_vars
    /\ Init_data_vars
    /\ Init_collect_vars
    /\ Init_lease_vars
    /\ Init_commit_vars
    /\ step = 0 /\ step_x = "init" /\ number_refreshes = 0

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Message manipulation   }\end{center}           *)
(* ^'                                                                      *)
(***************************************************************************)

\* Note: Variable message_history has impact in performace, update only when debugging.

\* Add message m to the network msgs.
WithMessage(m, msgs) ==
    Append(msgs, m)
    
\* Remove message m from the network msgs.
WithoutMessage(m, msgs) ==
    Remove(msgs, m)

\* Adds the message m to the network.
\* Variables changed: messages, message_history.
Send(m) ==
    /\ messages' = WithMessage(m, messages)
    /\ message_history' = message_history \union {m}
    \*/\ UNCHANGED message_history

\* Adds a set of messages to the network.
\* Variables changed: messages, message_history.
Send_set(m_set) ==
    /\ messages' = messages \o SetToSeq(m_set)
    /\ message_history' = message_history \union m_set
    \*/\ UNCHANGED message_history    
    
\* Removes the request from network and adds a set of messages.
\* Variables changed: messages, message_history.    
Reply_set(response_set, request) ==
    /\ messages' = WithoutMessage(request, messages) \o SetToSeq(response_set)
    /\ message_history' = message_history \union response_set
    \*/\ UNCHANGED message_history    
    
\* Removes message m from the network.
\* Variables changed: messages, message_history.
Discard(m) ==
    /\ messages' = WithoutMessage(m, messages)
    /\ UNCHANGED message_history
    
\* Removes the request from network and adds the response.
\* Variables changed: messages, message_history.
Reply(response, request) ==
    /\ messages' = WithoutMessage(request, WithMessage(response, messages))
    /\ message_history' = message_history \union {response}
    \*/\ UNCHANGED message_history

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Helper predicates   }\end{center}              *)
(* ^'                                                                      *)
(***************************************************************************)

\* Compute a new unique proposal number for a given monitor.
\* Example: oldpn = 305, rank(mon) = 5, newpn = 405.
get_new_proposal_number(mon, oldpn) ==
    ((oldpn \div 100) + 1) * 100 + rank(mon)

\* Clear the variable peer_first_committed.
\* Variables changed: peer_first_committed.
clear_peer_first_committed(mon) ==
    peer_first_committed' = [peer_first_committed EXCEPT ![mon] =
                                [m \in Monitors |-> -1]]

\* Clear the variable peer_last_committed.
\* Variables changed: peer_last_committed.
clear_peer_last_committed(mon) ==
    peer_last_committed' = [peer_last_committed EXCEPT ![mon] =
                                [m \in Monitors |-> -1]]

\* Store peer values and update first_committed, last_committed and monitor_store accordingly.
\* Variables changed: values, first_committed, last_committed, monitor_store.
store_state(mon,msg) ==
    \* Choose peer values from mon last committed +1 to peer last committed.
    /\ LET logs == (DOMAIN msg.values) \intersect (last_committed[mon]+1..msg.last_committed)
       IN /\ values' = [values EXCEPT ![mon] =
               [i \in DOMAIN values[mon] \union logs |->
                   IF i \notin DOMAIN values[mon]
                   THEN msg.values[i]
                   ELSE values[mon][i] ]]
          \* Update last committed and first committed.
          /\ last_committed' = [last_committed EXCEPT ![mon] = Max(logs \union {last_committed[mon]})]
          /\ IF logs # {} /\ first_committed[mon] = 0
             THEN first_committed' =
                        [first_committed EXCEPT ![mon] = Min(logs)]
             ELSE first_committed' =
                        [first_committed EXCEPT ![mon] = Min(logs \union {first_committed[mon]})]
    \* Update monitor store.
    /\ IF last_committed'[mon] = 0
       THEN UNCHANGED monitor_store
       ELSE monitor_store' = [monitor_store EXCEPT ![mon] = values'[mon][last_committed'[mon]]]

\* Check if uncommitted value version is still valid, else reset it.
\* Variables changed: uncommitted_v, uncommitted_value.
check_and_correct_uncommitted(mon) ==
    IF uncommitted_v[mon] <= last_committed'[mon]
    THEN /\ uncommitted_v' = [uncommitted_v EXCEPT ![mon] = 0]
         /\ uncommitted_value' = [uncommitted_value EXCEPT ![mon] = Nil]
    ELSE UNCHANGED <<uncommitted_v, uncommitted_value>>

\* Trigger new election by incrementing epoch.
\* Variables changed: epoch.
bootstrap ==
    /\ epoch' = epoch + 1

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Lease phase predicates   }\end{center}         *)
(* ^'                                                                      *)
(***************************************************************************)

\* Changes mon state to STATE_ACTIVE.
\* Variables changed: state.
finish_round(mon) ==
    /\ isLeader[mon] = TRUE
    /\ state' = [state EXCEPT ![mon] = STATE_ACTIVE]

\* Resets the variable acked lease and adds events to send lease messages to peers.
\* Variables changed: acked_lease, messages, message_history, phase.
extend_lease(mon) ==
    /\ isLeader[mon] = TRUE
    /\ acked_lease' = [acked_lease EXCEPT ![mon] =
        [m \in Monitors |-> IF m = mon THEN TRUE ELSE FALSE]]
        
    /\ Send_set(
        {[type           |-> OP_LEASE,
          from           |-> mon,
          dest           |-> dest,
          last_committed |-> last_committed[mon]]: dest \in (Monitors \ {mon})
         })
        
    /\ phase' = [phase EXCEPT ![mon] = PHASE_LEASE]

\* Handle a lease message. The peon changes his state and replies with a lease ack message.
\* The reply is commented because the lease ack is only used to check if all peers are up.
\* In the model this is done by "randomly" triggering the predicate Timeout. In this way, the search space is reduced.
\* Variables changed: messages, message_history, state.
handle_lease(mon, msg) ==
    /\ \* discard if not peon or peon is behind
       IF \/ isLeader[mon] = TRUE
          \/ last_committed[mon] # msg.last_committed
       THEN /\ Discard(msg)
            /\ UNCHANGED state
       ELSE /\ state' = [state EXCEPT ![mon] = STATE_ACTIVE]
            (*/\ Reply([type          |-> OP_LEASE_ACK,
                      from            |-> mon,
                      dest            |-> msg.from,
                      first_committed |-> first_committed[mon],
                      last_committed  |-> last_committed[mon]],msg)*)
            /\ Discard(msg)
    /\ UNCHANGED <<epoch, isLeader, phase>>
    /\ UNCHANGED <<restart_vars, data_vars, collect_vars, lease_vars, commit_vars>>

\* Handle a lease ack message. The leader updates the acked_lease variable.
\* Once the lease_ack messages are not sent, this predicate is never called.
\* The reasoning for this is given in handle_lease comment.
\* Variables changed: acked_lease, messages, message_history.
handle_lease_ack(mon, msg) ==
    /\ phase[mon] = PHASE_LEASE
    /\ acked_lease' = [acked_lease EXCEPT ![mon] =
        [acked_lease[mon] EXCEPT ![msg.from] = TRUE]]
    /\ Discard(msg)
    /\ UNCHANGED <<epoch>>
    /\ UNCHANGED <<state_vars, restart_vars, data_vars, collect_vars, commit_vars>>

\* Predicate that is called when all peers ack the lease. The phase is changed to prevent loops.
\* Once the lease_ack messages are not sent, this predicate is never called.
\* The reasoning for this is given in handle_lease comment.
\* Variables changed: phase.
post_lease_ack(mon) ==
    /\ phase[mon] = PHASE_LEASE
    /\ phase' = [phase EXCEPT ![mon] = PHASE_LEASE_DONE]
    /\ \A m \in Monitors: acked_lease[mon][m] = TRUE
    /\ UNCHANGED <<isLeader, state>>
    /\ UNCHANGED <<global_vars, restart_vars, data_vars, collect_vars,
                   lease_vars, commit_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Commit phase predicates   }\end{center}        *)
(* ^'                                                                      *)
(***************************************************************************)

\* Start a commit phase by the leader. The variable new_value is assigned and the events to send
\* begin messages to the peers are added to send_queue.
\* The value of uncommitted_v and uncommitted_value are assigned in order for the leader to be
\* able to recover from a crash/restart.
\* Variables changed: accepted, new_value, phase, messages, message_history, values, uncommitted_v, uncommitted_value.
begin(mon, v) ==
    /\ isLeader[mon] = TRUE
    /\ \/ state'[mon] = STATE_UPDATING
       \/ state'[mon] = STATE_UPDATING_PREVIOUS
    /\ Len(ranks) = 1 \/ num_last[mon] > Len(ranks) \div 2
    /\ new_value[mon] = Nil
    /\ accepted' = [accepted EXCEPT ![mon] =
        [m \in Monitors |-> IF m = mon THEN TRUE ELSE FALSE]]
    /\ new_value' = [new_value EXCEPT ![mon] = v]
    /\ phase' = [phase EXCEPT ![mon] = PHASE_BEGIN]
    /\ values' = [values EXCEPT ![mon] =
        (values[mon] @@ ((last_committed[mon] + 1) :> new_value'[mon])) ]
        
    /\ Send_set(
        {[type           |-> OP_BEGIN,
          from           |-> mon,
          dest           |-> dest,
          last_committed |-> last_committed[mon],
          values         |-> values'[mon],
          pn             |-> accepted_pn[mon]]: dest \in (Monitors \ {mon})
         })
             
    /\ uncommitted_v' = [uncommitted_v EXCEPT ![mon] = last_committed[mon]+1]
    /\ uncommitted_value' = [uncommitted_value EXCEPT ![mon] = v]

\* Handle a begin message. The monitor will accept if the proposal number in the message is greater
\* or equal than the one he accepted.
\* Similar to what happens in begin, uncommitted_v and uncommitted_value are assigned in order for
\* the monitor to recover in case of a crash/restart.
\* Variables changed: messages, message_history, state, values, uncommitted_v, uncommitted_value.
handle_begin(mon, msg) ==
    /\ isLeader[mon] = FALSE
    /\ IF msg.pn < accepted_pn[mon]
       THEN
        /\ Discard(msg)
        /\ UNCHANGED <<state, restart_vars>>
       ELSE
        /\ msg.pn = accepted_pn[mon]
        /\ msg.last_committed = last_committed[mon]

        \* assign values[mon][last_committed[mon]+1]
        /\ values' = [values EXCEPT ![mon] =
            (values[mon] @@ ((last_committed[mon] + 1) :> msg.values[last_committed[mon] + 1])) ]

        /\ state' = [state EXCEPT ![mon] = STATE_UPDATING]
        /\ uncommitted_v' = [uncommitted_v EXCEPT ![mon] = last_committed[mon]+1]
        /\ uncommitted_value' = [uncommitted_value EXCEPT ![mon] =
            values'[mon][last_committed[mon]+1]]

        /\ Reply([type            |-> OP_ACCEPT,
                  from            |-> mon,
                  dest            |-> msg.from,
                  last_committed  |-> last_committed[mon],
                  pn              |-> accepted_pn[mon]],msg)

    /\ UNCHANGED <<epoch, isLeader, phase, monitor_store, accepted_pn, first_committed,
                   last_committed>>
    /\ UNCHANGED <<collect_vars, lease_vars, commit_vars>>

\* Handle an accept message. If the leader receives a positive response from the peer, it will
\* add it to the variable accepted.
\* Variables changed: messages, message_history, accepted
handle_accept(mon, msg) ==
    /\ isLeader[mon] = TRUE
    /\ \/ state[mon] = STATE_UPDATING_PREVIOUS
       \/ state[mon] = STATE_UPDATING
    /\ phase[mon] = PHASE_BEGIN
    /\ new_value[mon] # Nil
    /\ IF \/ msg.pn # accepted_pn[mon]
          \/ /\ last_committed[mon] > 0
             /\ msg.last_committed < last_committed[mon]-1
       THEN
        /\ Discard(msg)
        /\ UNCHANGED accepted
       ELSE
        /\ accepted' = [accepted EXCEPT ![mon] =
                [accepted[mon] EXCEPT ![msg.from] = TRUE]]
        /\ Discard(msg)
    /\ UNCHANGED <<epoch, pending_proposal, new_value>>
    /\ UNCHANGED <<restart_vars, state_vars, data_vars, collect_vars, lease_vars>>

\* Predicate that is enabled and called when all peers accept begin request from leader.
\* The leader commits the transaction in new_value and adds events in send_queue to send commit messages
\* to his peers.
\* Variables changed: first_committed, last_committed, monitor_store, new_value, messages, message_history, state, phase
post_accept(mon) ==
    /\ phase[mon] = PHASE_BEGIN
    /\ \A m \in Monitors: accepted[mon][m] = TRUE
    /\ new_value[mon] # Nil
    /\ \/ state[mon] = STATE_UPDATING_PREVIOUS
       \/ state[mon] = STATE_UPDATING

    /\ last_committed' = [last_committed EXCEPT ![mon] = last_committed[mon] + 1]
    /\ IF first_committed[mon] = 0
       THEN first_committed' = [first_committed EXCEPT ![mon] = first_committed[mon] + 1]
       ELSE UNCHANGED first_committed

    /\ monitor_store' = [monitor_store EXCEPT ![mon] = values[mon][last_committed[mon]+1]]
    /\ new_value' = [new_value EXCEPT ![mon] = Nil]
    
    /\ Send_set(
        {[type           |-> OP_COMMIT,
          from           |-> mon,
          dest           |-> dest,
          last_committed |-> last_committed'[mon],
          pn             |-> accepted_pn[mon],
          values         |-> values[mon]]: dest \in (Monitors \ {mon})
         })
                 
    /\ state' = [state EXCEPT ![mon] = STATE_REFRESH]
    /\ phase' = [phase EXCEPT ![mon] = PHASE_COMMIT]
    /\ UNCHANGED <<isLeader, values, accepted_pn, pending_proposal, accepted>>
    /\ UNCHANGED <<epoch, restart_vars, collect_vars, lease_vars>>

\* Predicate that is called after post_accept. The leader finishes the commit phase by updating his state to
\* STATE_ACTIVE and by extending the lease to his peers.
\* Variables changed: state, phase, acked_lease, messages, message_history.
finish_commit(mon) ==
    /\ state[mon] = STATE_REFRESH
    /\ phase[mon] = PHASE_COMMIT
    /\ finish_round(mon)
    /\ extend_lease(mon)
    /\ UNCHANGED <<epoch, isLeader>>
    /\ UNCHANGED <<restart_vars, data_vars, collect_vars, commit_vars>>

\* Handle a commit message. The monitor stores the values sent by the leader commit message.
\* Variables changed: messages, message_history, values, first_committed, last_committed, monitor_store, uncommitted_v,
\* uncommitted_value.
handle_commit(mon, msg) ==
    /\ isLeader[mon] = FALSE
    /\ store_state(mon, msg)
    /\ check_and_correct_uncommitted(mon)
    /\ Discard(msg)
    /\ UNCHANGED <<epoch, accepted_pn>>
    /\ UNCHANGED <<state_vars, collect_vars, lease_vars, commit_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Client Request   }\end{center}                 *)
(* ^'                                                                      *)
(***************************************************************************)

\* Request a transaction v to the monitor. The transaction is saved on pending proposal to be committed in
\* the next available commit phase.
\* This predicate has a big cost on performance, so there were some requirements added (monitor phase and state)
\* to mitigate that.
\* Variables changed: pending_proposal.
client_request(mon, v) ==
    /\ phase[mon] = PHASE_LEASE \/ phase[mon] = PHASE_ELECTION
    /\ isLeader[mon] = TRUE
    /\ state[mon] = STATE_ACTIVE
    /\ pending_proposal[mon] = Nil
    /\ pending_proposal' = [pending_proposal EXCEPT ![mon] = v]
    /\ UNCHANGED <<new_value, accepted>>
    /\ UNCHANGED <<global_vars, state_vars, restart_vars, data_vars, collect_vars, lease_vars>>

\* Start a commit phase with the value on pending proposal.
\* Variables changed: state, pending_proposal, accepted, new_value, phase, messages, message_history, values, uncommitted_v,
\* uncommitted_value.
propose_pending(mon) ==
    /\ phase[mon] = PHASE_LEASE \/ phase[mon] = PHASE_ELECTION
    /\ state[mon] = STATE_ACTIVE
    /\ pending_proposal[mon] # Nil
    /\ pending_proposal' = [pending_proposal EXCEPT ![mon] = Nil]
    /\ state' = [state EXCEPT ![mon] = STATE_UPDATING]
    /\ begin(mon, pending_proposal[mon])
    /\ UNCHANGED <<isLeader, monitor_store, accepted_pn, first_committed, last_committed>>
    /\ UNCHANGED <<epoch, collect_vars, lease_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Collect phase predicates   }\end{center}       *)
(* ^'                                                                      *)
(***************************************************************************)

\* Start collect phase. This first part of the collect phase is divided in two parts (collect and pre_send_collect)
\* in order to simplify variable changes (when collect is triggered from handle_last).
\* Variables changed: accepted_pn, phase.
collect(mon, oldpn) ==
    /\ state[mon] = STATE_RECOVERING
    /\ isLeader[mon] = TRUE
    /\ LET new_pn == get_new_proposal_number(mon, Max({oldpn,accepted_pn[mon]}))
       IN  /\ accepted_pn' = [accepted_pn EXCEPT ![mon] = new_pn]
    /\ phase' = [phase EXCEPT ![mon] = PHASE_PRE_COLLECT]

\* Continue the start of the collect phase. Initialize the number of peers that accepted the proposal (num_last) and
\* the variables with peers version numbers. Check if there is an uncommitted value.
\* Add events to send_queue to send collect messages to the peers.
\* Variables changed: peer_first_committed, peer_last_committed, uncommitted_v, uncommitted_value, num_last,
\* messages, message_history, phase.
pre_send_collect(mon) ==
    /\ state[mon] = STATE_RECOVERING
    /\ isLeader[mon] = TRUE
    /\ phase[mon] = PHASE_PRE_COLLECT
    /\ clear_peer_first_committed(mon)
    /\ clear_peer_last_committed(mon)

    /\ IF last_committed[mon]+1 \in DOMAIN values[mon]
       THEN /\ uncommitted_v' =
                [uncommitted_v EXCEPT ![mon] = last_committed[mon]+1]
            /\ uncommitted_value' =
                [uncommitted_value EXCEPT ![mon] = values[mon][last_committed[mon]+1]]
       ELSE UNCHANGED <<restart_vars>>

    /\ num_last' = [num_last EXCEPT ![mon] = 1]
    
    /\ Send_set(
        {[type            |-> OP_COLLECT,
          from            |-> mon,
          dest            |-> dest,
          first_committed |-> first_committed[mon],
          last_committed  |-> last_committed[mon],
          pn              |-> accepted_pn[mon]]: dest \in (Monitors \ {mon})
         })
        
    /\ phase' = [phase EXCEPT ![mon] = PHASE_COLLECT]
    /\ UNCHANGED <<isLeader, state>>
    /\ UNCHANGED <<epoch, data_vars, lease_vars, commit_vars>>

\* Handle a collect message. The peer will accept the proposal number from the leader if it is bigger than the last
\* proposal number he accepted.
\* Variables changed: messages, message_history, epoch, state, accepted_pn
handle_collect(mon, msg) ==
    /\ isLeader[mon] = FALSE
    /\ state' = [state EXCEPT ![mon] = STATE_RECOVERING]
    /\ \/ /\ msg.first_committed > last_committed[mon] + 1
          /\ bootstrap
          /\ Discard(msg)
          /\ UNCHANGED <<accepted_pn>>
       \/ /\ msg.first_committed <= last_committed[mon] + 1
          /\ IF msg.pn > accepted_pn[mon]
             THEN accepted_pn' = [accepted_pn EXCEPT ![mon] = msg.pn]
             ELSE UNCHANGED accepted_pn
          /\ Reply([type            |-> OP_LAST,
                    from            |-> mon,
                    dest            |-> msg.from,
                    first_committed |-> first_committed[mon],
                    last_committed  |-> last_committed[mon],
                    values          |-> values[mon],
                    pn              |-> accepted_pn'[mon]],msg)
          /\ UNCHANGED epoch
    /\ UNCHANGED <<isLeader, phase, values, first_committed, last_committed, monitor_store>>
    /\ UNCHANGED <<restart_vars, collect_vars, lease_vars, commit_vars>>

\* Handle a last message (response from a peer to the leader collect message).
\* The peers first and last committed version are stored. If the leader is behind bootstraps. Stores any value that
\* the peer may have committed (store_state). If peer is behind send commit message with leader values.
\* If peer accepted proposal number increase num last, if he sent a bigger proposal number start a new collect phase with that.
\* Variables changed: messages, message_history, epoch, phase, uncommitted_v, uncommitted_value, monitor_store, values,
\* accepted_pn, first_committed, last_committed, num_last, peer_first_committed, peer_last_committed.
handle_last(mon,msg) ==
    /\ isLeader[mon] = TRUE

    /\ peer_first_committed' = [peer_first_committed EXCEPT ![mon] =
        [peer_first_committed[mon] EXCEPT ![msg.from] = msg.first_committed]]
    /\ peer_last_committed' = [peer_last_committed EXCEPT ![mon] =
        [peer_last_committed[mon] EXCEPT ![msg.from] = msg.last_committed]]

    /\ IF msg.first_committed > last_committed[mon] + 1
       THEN
        /\ bootstrap
        /\ Discard(msg)
        /\ UNCHANGED <<num_last, accepted_pn, values, phase, monitor_store>>
        /\ UNCHANGED <<first_committed, last_committed, restart_vars>>
       ELSE
        /\ store_state(mon, msg)
        /\ IF \E peer \in Monitors:
                /\ peer # mon
                /\ peer_last_committed'[mon][peer] # -1
                /\ peer_last_committed'[mon][peer] + 1 < first_committed[mon]
                /\ first_committed[mon] > 1
           THEN
            /\ bootstrap
            /\ check_and_correct_uncommitted(mon)
            /\ Discard(msg)
            /\ UNCHANGED <<phase, accepted_pn, num_last>>
           ELSE
            /\ LET monitors_behind == {peer \in Monitors:
                    /\ peer # mon
                    /\ peer_last_committed'[mon][peer] # -1
                    /\ peer_last_committed'[mon][peer] < last_committed[mon]}
               IN Reply_set(
                    {[type           |-> OP_COMMIT,
                      from           |-> mon,
                      dest           |-> dest,
                      last_committed |-> last_committed'[mon],
                      pn             |-> accepted_pn[mon],
                      values         |-> values[mon]]: dest \in monitors_behind
                    }, msg)

            /\ \/ /\ msg.pn > accepted_pn[mon]
                  /\ collect(mon, msg.pn)
                  /\ check_and_correct_uncommitted(mon)
                  /\ UNCHANGED num_last
                  
               \/ /\ msg.pn = accepted_pn[mon]
                  /\ num_last' = [num_last EXCEPT ![mon] = num_last[mon] + 1]

                  /\ IF /\ msg.last_committed+1 \in DOMAIN msg.values
                        /\ msg.last_committed >= last_committed'[mon]
                        /\ msg.last_committed+1 >= uncommitted_v[mon]
                     THEN /\ uncommitted_v' =
                                [uncommitted_v EXCEPT ![mon] = msg.last_committed+1]
                          /\ uncommitted_value' =
                                [uncommitted_value EXCEPT ![mon] = msg.values[msg.last_committed+1]]
                     ELSE check_and_correct_uncommitted(mon)

                  /\ UNCHANGED <<phase, accepted_pn>>
                  
               \/ /\ msg.pn < accepted_pn[mon]
                  /\ check_and_correct_uncommitted(mon)
                  /\ UNCHANGED <<phase, accepted_pn, num_last>>
            /\ UNCHANGED epoch
       /\ UNCHANGED <<epoch>>
       
    /\ UNCHANGED <<isLeader, state>>
    /\ UNCHANGED <<lease_vars, commit_vars>>

\* Predicate that is enabled and called when all peers accept collect request from leader. If there is an uncommitted value,
\* a commit phase is started with that value, else the leader changes to ACTIVE_STATE and extends the lease to his peers.
\* Variables changed: peer_first_committed, peer_last_committed, state, accepted, new_value, phase, messages, message_history,
\* values, uncommitted_v, uncommitted_value, acked_lease.
post_last(mon) ==
    /\ isLeader[mon] = TRUE
    /\ num_last[mon] = Len(ranks)
    /\ phase[mon] = PHASE_COLLECT

    /\ clear_peer_first_committed(mon)
    /\ clear_peer_last_committed(mon)

    /\ IF /\ uncommitted_v[mon] = last_committed[mon]+1
          /\ uncommitted_value[mon] # Nil
       THEN /\ state' = [state EXCEPT ![mon] = STATE_UPDATING_PREVIOUS]
            /\ begin(mon, uncommitted_value)
            /\ UNCHANGED <<acked_lease>>
       ELSE /\ finish_round(mon)
            /\ extend_lease(mon)
            /\ UNCHANGED <<accepted, new_value, values, restart_vars>>

    /\ UNCHANGED <<isLeader, monitor_store, accepted_pn, first_committed, last_committed>>
    /\ UNCHANGED <<epoch, num_last, pending_proposal>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Leader election   }\end{center}                *)
(* ^'                                                                      *)
(***************************************************************************)

\* Elect one monitor as a leader and initialize the remaining ones as peons.
\* Variables changed: isLeader, state, phase, new_value, pending_proposal, epoch.
leader_election ==
    /\ \E mon \in Monitors:
        /\ isLeader' = [m \in Monitors |-> IF m = mon THEN TRUE ELSE FALSE]
        /\ state' = [m \in Monitors |->
            IF Len(ranks) = 1 THEN STATE_ACTIVE ELSE STATE_RECOVERING]
    /\ phase' = [m \in Monitors |-> PHASE_ELECTION]
    /\ new_value' = [m \in Monitors |-> Nil]
    /\ pending_proposal' = [m \in Monitors |-> Nil]
    /\ epoch' = epoch + 1
    /\ UNCHANGED <<accepted, messages, message_history>>
    /\ UNCHANGED <<data_vars, restart_vars, collect_vars, lease_vars>>

\* Start recovery phase if number of monitors is greater than 1.
\* Variables changed: accepted_pn, phase.
election_recover(mon) ==
    /\ Len(ranks) > 1
    /\ phase[mon] = PHASE_ELECTION
    /\ collect(mon,0)
    /\ UNCHANGED <<isLeader, state, values, first_committed, last_committed, monitor_store>>
    /\ UNCHANGED <<global_vars, restart_vars, collect_vars, lease_vars, commit_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Timeouts and restart   }\end{center}           *)
(* ^'                                                                      *)
(***************************************************************************)

\* Restart a monitor and wipe variables that are not persistent.
\* Variables changed: messages, isLeader, phase, state, pending_proposal, new_value, number_refreshes.
restart_mon(mon) ==
    /\ number_refreshes = 0
        => /\ isLeader[mon] = FALSE /\ \A monx \in Monitors: num_last[mon] < 2
           /\ \E i \in 1..Len(messages): messages[i].type = OP_LAST /\ messages[i].from = mon
    /\ messages' = SelectSeq(messages, LAMBDA t: t.from # mon)
    /\ isLeader' = [isLeader EXCEPT ![mon] = FALSE]
    /\ phase' = [phase EXCEPT ![mon] = PHASE_ELECTION]
    /\ state' = [state EXCEPT ![mon] = IF Len(ranks) = 1
                                       THEN STATE_ACTIVE
                                       ELSE STATE_RECOVERING]
    /\ pending_proposal' = [pending_proposal EXCEPT ![mon] = Nil]
    /\ new_value' = [new_value EXCEPT ![mon] = Nil]
    /\ number_refreshes' = number_refreshes+1
    /\ UNCHANGED <<epoch, message_history, accepted>>
    /\ UNCHANGED <<restart_vars, data_vars, collect_vars, lease_vars>>

\* Monitor timeout (simulate message not received). Triggers new elections.
\* Messages in network and events in send_queue are cleared.
\* Variables changed: epoch, send_queue, messages.
Timeout(mon) ==
    /\ phase[mon] = PHASE_COLLECT \/ phase[mon] = PHASE_BEGIN
    /\ bootstrap
    /\ messages' = <<>>
    /\ UNCHANGED <<message_history, state_vars, restart_vars, data_vars, collect_vars,
                   lease_vars, commit_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Dispatchers and next statement   }\end{center} *)
(* ^'                                                                      *)
(***************************************************************************)

\* Handle a message.
Receive(msg) ==
    /\ \/ phase[msg.dest] = PHASE_COLLECT
       \/ phase[msg.dest] = PHASE_BEGIN
       \/ phase[msg.dest] = PHASE_ELECTION
    /\
       \/ /\ msg.type = OP_COLLECT
          /\ handle_collect(msg.dest, msg)
          /\ step_x' = "receive collect"

       \/ /\ msg.type = OP_LAST
          /\ handle_last(msg.dest, msg)
          /\ step_x' = "receive last"

       \/ /\ msg.type = OP_LEASE
          /\ handle_lease(msg.dest, msg)
          /\ step_x' = "receive lease"

       \/ /\ msg.type = OP_LEASE_ACK
          /\ handle_lease_ack(msg.dest, msg)
          /\ step_x' = "receive lease_ack"

       \/ /\ msg.type = OP_BEGIN
          /\ handle_begin(msg.dest, msg)
          /\ step_x' = "receive begin"

       \/ /\ msg.type = OP_ACCEPT
          /\ handle_accept(msg.dest, msg)
          /\ step_x' = "receive accept"

       \/ /\ msg.type = OP_COMMIT
          /\ handle_commit(msg.dest, msg)
          /\ step_x' = "receive commit"

\* Limit some variables to reduce search space.    
reduce_search_space ==
    /\ epoch # 6 /\ number_refreshes # 3
    /\ \A mon \in Monitors: last_committed[mon] < 2
       \*=> \A mon2 \in Monitors: new_value[mon2] = Nil
    /\ \A mon \in Monitors: accepted_pn[mon] < 300    

\* State transitions.
Next ==
    /\ reduce_search_space
    /\ IF epoch % 2 = 1 THEN
        /\ leader_election
        /\ step_x' = "election" /\ step' = step+1
        /\ UNCHANGED number_refreshes
       ELSE
        \/
           /\ \E mon \in Monitors: election_recover(mon)
           /\ step_x' = "election_recover" /\ step' = step+1
           /\ UNCHANGED number_refreshes

        \/ /\ \E mon \in Monitors: pre_send_collect(mon)
           /\ step_x' = "pre_send_collect"  /\ step' = step+1
           /\ UNCHANGED number_refreshes

        \/ /\ \E mon \in Monitors: post_last(mon)
           /\ step_x' = "post_last" /\ step' = step+1
           /\ UNCHANGED number_refreshes

        \/ /\ \E mon \in Monitors: post_lease_ack(mon)
           /\ step_x' = "post_lease_ack" /\ step' = step+1
           /\ UNCHANGED number_refreshes

        \/ /\ \E mon \in Monitors: post_accept(mon)
           /\ step_x' = "post_accept" /\ step' = step+1
           /\ UNCHANGED number_refreshes

        \/ /\ \E mon \in Monitors: finish_commit(mon)
           /\ step_x' = "finish_commit" /\ step' = step+1
           /\ UNCHANGED number_refreshes

        \/ /\ \E mon \in Monitors: \E v \in Value_set: client_request(mon, v)
           /\ step_x' = "client_request" /\ step' = step+1
           /\ UNCHANGED number_refreshes

        \/ /\ \E mon \in Monitors: propose_pending(mon)
           /\ step_x' = "propose_pending" /\ step' = step+1
           /\ UNCHANGED number_refreshes

        \/ /\ \E i \in 1..Len(messages): Receive(messages[i])
           /\ step' = step+1
           /\ UNCHANGED number_refreshes

        \/ /\ \E mon \in Monitors: restart_mon(mon)
           /\ step_x' = "restart mon" /\ step' = step+1

        \/ /\ \E mon \in Monitors: Timeout(mon)
           /\ step_x' = "timeout and restart" /\ step' = step+1
           /\ UNCHANGED number_refreshes


(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Test/Debug invariants   }\end{center}          *)
(* ^'                                                                      *)
(***************************************************************************)

\* Invariant used to search for a state where 'x' happens.
Inv_find_state(x) == ~x

\* Invariant used to search for a behavior of diameter equal to 'size'.
Inv_diam(size) == step # size-1

\* Invariants to test in model check
Inv == /\ TRUE
       \*/\ Inv_diam(20)

(*
Examples:

Find a behavior with a diameter of size 60.
Inv_diam(60)

Find a behavior where two different monitors assume the role of a leader.
Inv_find_state(
    \E msg1, msg2 \in message_history:
        /\ msg1.type = OP_COLLECT /\ msg2.type = OP_COLLECT
        /\ msg1.from # msg2.from
)

Find a state where a monitor crashed during the collect phase and fails to send a OP_LAST message.
Inv_find_state(
    /\ step_x="restart mon"

    \* The system is in collect phase and no OP_LAST message has been received.
    \* isLeader[mon] = TRUE assures that the leader was not the one that crashed.
    /\ \E mon \in Monitors:
        /\ isLeader[mon] = TRUE
        /\ phase[mon] = PHASE_COLLECT
        /\ num_last[mon] = 1

    \* All the collect requests have been handled by the peers.
    /\ \A i \in 1..Len(messages):
        messages[i].type # OP_COLLECT

    /\ epoch = 2
)

Find a state where the leader crashes during the commit phase, failing to complete the commit.
Inv_find_state(
    /\ step_x="restart mon"
    /\ \E i \in 1..Len(messages):
        messages[i].type = OP_ACCEPT
    /\ \A mon \in Monitors:
        isLeader[mon] = FALSE
    /\ epoch = 2
)
Note: After finding a state, that complete state can be used as an initial state to analyze behaviors from there.
*)


=============================================================================
\* Modification History
\* Last modified Tue Mar 09 16:00:11 WET 2021 by afonsonf
\* Created Mon Jan 11 16:15:26 WET 2021 by afonsonf