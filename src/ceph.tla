------------------------------- MODULE ceph -------------------------------
(***************************************************************************)
(* `^                                                                      *)
(*                                                                         *)
(* This is a specification of the paxos algorithm implemented in Ceph.     *)
(* The specification is based on the following source file:                *)
(* https://github.com/ceph/ceph/blob/master/src/mon/Paxos.cc \newline      *)
(*                                                                         *)
(* For a more detailed overview of the specification:                      *)
(* https://github.com/afonsonf/ceph-consensus-spec                         *)
(*                                                                         *)
(* ^'                                                                      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences, TLC

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Utils   }                                                    *)
(*  ^'                                                                     *)
(***************************************************************************)

\* Max element from a set.
\* @type: Set(Int) => Int;
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

\* Min element from a set.
\* @type: Set(Int) => Int;
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

\* Set of monitors to a sequence.
RECURSIVE SetToSeq(_)
\* @type: Set(MONITOR) => Seq(MONITOR);
SetToSeq(S) ==
    IF S = {} THEN <<>>
              ELSE LET x == CHOOSE x \in S: TRUE
                   IN <<x>> \o SetToSeq(S \ {x})

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Constants   }                                                *)
(*  ^'                                                                     *)
(***************************************************************************)

\* Set of Monitors.
CONSTANTS (*@type: Set(MONITOR);*) Monitors

\* Sequence of monitors.
\* @type: Seq(MONITOR);
MonitorsSeq == TLCEval(SetToSeq(Monitors))

\* Number of monitors.
\* @type: Int;
MonitorsLen == TLCEval(Len(MonitorsSeq))

\* Rank predicate, used to compute proposal numbers.
\* @type: MONITOR => Int;
rank(mon) == CHOOSE i \in 1..MonitorsLen: MonitorsSeq[i]=mon

\* Set of possible values.
CONSTANTS (*@type: Set(VALUE);*) Value_set

\* Predicate used in the cfg file to define the symmetry set.
\* Workaround for typechecker.
\* @typeAlias: MONITOR = T;
\* @typeAlias: VALUE = T;
SYMM == Permutations(Monitors) \union Permutations(Value_set)

\* Reserved value.
CONSTANTS (*@type: VALUE;*) Nil

\* Paxos states.
CONSTANTS (*@type: STATE_NAME;*) STATE_RECOVERING,(*@type: STATE_NAME;*) STATE_ACTIVE,
          (*@type: STATE_NAME;*) STATE_UPDATING, (*@type: STATE_NAME;*) STATE_UPDATING_PREVIOUS,
          (*@type: STATE_NAME;*) STATE_WRITING, (*@type: STATE_NAME;*) STATE_WRITING_PREVIOUS,
          (*@type: STATE_NAME;*) STATE_REFRESH, (*@type: STATE_NAME;*) STATE_SHUTDOWN

\* Paxos auxiliary phase states.
\* They are used to force some sequence of steps.
CONSTANTS (*@type: PHASE_NAME;*) PHASE_ELECTION,
          (*@type: PHASE_NAME;*) PHASE_SEND_COLLECT, (*@type: PHASE_NAME;*) PHASE_COLLECT,
          (*@type: PHASE_NAME;*) PHASE_LEASE, (*@type: PHASE_NAME;*) PHASE_LEASE_DONE,
          (*@type: PHASE_NAME;*) PHASE_BEGIN, (*@type: PHASE_NAME;*) PHASE_COMMIT

\* Paxos message types.
CONSTANTS (*@type: MESSAGE_OP;*) OP_COLLECT, (*@type: MESSAGE_OP;*) OP_LAST,
          (*@type: MESSAGE_OP;*) OP_BEGIN, (*@type: MESSAGE_OP;*) OP_ACCEPT,
          (*@type: MESSAGE_OP;*) OP_COMMIT,
          (*@type: MESSAGE_OP;*) OP_LEASE, (*@type: MESSAGE_OP;*) OP_LEASE_ACK

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Global variables   }                                         *)
(* ^'                                                                      *)
(***************************************************************************)

\* Integer representing the current epoch. If is odd trigger an election.
VARIABLE (*@type: Int;*) epoch

\* Store messages waiting to be handled.
VARIABLE (*@type: MONITOR -> (MONITOR -> Seq(MESSAGE));*) messages

\* Stores history of messages. Can be useful to find specific states.
VARIABLE (*@type: Set(MESSAGE);*) message_history

\* Stores if a monitor is up or down. All available monitors, in a given epoch, are part of the quorum.
VARIABLE (*@type: MONITOR -> Bool;*) quorum

\* Size of the current quorum.
VARIABLE (*@type: Int;*) quorum_sz

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   State variables   }                                          *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores the current leader. isLeader[mon] is True iff mon is a leader, else False.
VARIABLE (*@type: MONITOR -> Bool;*) isLeader

\* A function that stores the state of each monitor.
VARIABLE (*@type: MONITOR -> STATE_NAME;*) state

\* A function that stores the phase of each monitor.
VARIABLE (*@type: MONITOR -> PHASE_NAME;*) phase

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Restart variables   }                                        *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores, for each monitor, a proposal number when the commit phase starts.
\* This proposal number can be retrieved after a monitor crashes and restarts.
VARIABLE (*@type: MONITOR -> PN;*) pending_pn

\* A function that stores, for each monitor, a value version when the commit phase starts.
\* This value version can be retrieved after a monitor crashes and restarts.
VARIABLE (*@type: MONITOR -> VALUE_VERSION;*) pending_v

\* A function that stores, for each monitor, the best uncommitted pn received in the collect phase.
VARIABLE (*@type: MONITOR -> PN;*) uncommitted_pn

\* A function that stores, for each monitor, the best uncommitted value version received in the collect phase.
VARIABLE (*@type: MONITOR -> VALUE_VERSION;*) uncommitted_v

\* A function that stores, for each monitor, the best uncommitted value received in the collect phase.
VARIABLE (*@type: MONITOR -> VALUE;*) uncommitted_value

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Data variables   }                                           *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores, for each monitor, the store where the transactions are applied.
\* In this model, a transaction represents changing the value in the store.
VARIABLE (*@type: MONITOR -> VALUE;*) monitor_store

\* A function that stores the transaction log of each monitor.
VARIABLE (*@type: MONITOR -> (VALUE_VERSION -> VALUE);*) values

\* A function that stores the last proposal number accepted by each monitor.
VARIABLE (*@type: MONITOR -> PN;*) accepted_pn

\* A function that stores the first value version committed by each monitor.
VARIABLE (*@type: MONITOR -> VALUE_VERSION;*) first_committed

\* A function that stores the last value version committed by each monitor.
VARIABLE (*@type: MONITOR -> VALUE_VERSION;*) last_committed

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Collect phase variables   }                                  *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores the number of peers that accepted a collect request.
VARIABLE (*@type: MONITOR -> Int;*) num_last

\* Used by leader when receiving responses in collect phase.
VARIABLE (*@type: MONITOR -> (MONITOR -> VALUE_VERSION);*) peer_first_committed

\* Used by leader when receiving responses in collect phase.
VARIABLE (*@type: MONITOR -> (MONITOR -> VALUE_VERSION);*) peer_last_committed

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Lease phase variables   }                                    *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores, for each monitor, which of the peers have acked the lease request.
VARIABLE (*@type: MONITOR -> (MONITOR -> Bool);*) acked_lease

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Commit phase variables   }                                   *)
(* ^'                                                                      *)
(***************************************************************************)

\* A function that stores, for each monitor, the value proposed by a client.
VARIABLE (*@type: MONITOR -> VALUE;*) pending_proposal

\* A function that stores, for each monitor, the value to be committed in the begin phase.
VARIABLE (*@type: MONITOR -> VALUE;*) new_value

\* A function that stores, for each monitor, which of the peers have acked the begin request.
VARIABLE (*@type: MONITOR -> (MONITOR -> Bool);*) accepted

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Debug variables   }                                          *)
(* ^'                                                                      *)
(***************************************************************************)

\* Variables to help debug a behavior.
\* step is the diameter of a behavior/path.
\* step_name the current predicate being called.
VARIABLE (*@type: Str;*) step_name

\* Variables to limit the number of monitors crashes that can occur over a behavior.
\* This variable is used to limit the search space.
VARIABLE (*@type: Int;*) number_crashes

(***************************************************************************)
(* `^ \centering                                                           *)
(* \textbf{   Variables initialization   }                                 *)
(* ^'                                                                      *)
(***************************************************************************)

\* @typeAlias: VALUE_VERSION = Int;
\* @typeAlias: PN = Int;

global_vars    == <<epoch, messages, message_history, quorum, quorum_sz>>
state_vars     == <<isLeader, state, phase>>
restart_vars   == <<pending_pn, pending_v, uncommitted_pn, uncommitted_v, uncommitted_value>>
data_vars      == <<monitor_store, values, accepted_pn, first_committed, last_committed>>
collect_vars   == <<num_last, peer_first_committed, peer_last_committed>>
lease_vars     == acked_lease
commit_vars    == <<pending_proposal, new_value, accepted>>

vars == <<global_vars, state_vars, restart_vars, data_vars, collect_vars,
          lease_vars, commit_vars>>

Init_global_vars ==
    /\ epoch = 1
    /\ messages = [mon1 \in Monitors |-> [mon2 \in Monitors |-> <<>>] ]
    /\ message_history = {}
    /\ quorum = [mon \in Monitors |-> TRUE]
    /\ quorum_sz = MonitorsLen

Init_state_vars ==
    /\ isLeader = [mon \in Monitors |-> FALSE]
    /\ state = [mon \in Monitors |-> STATE_RECOVERING]
    /\ phase = [mon \in Monitors |-> PHASE_ELECTION]

Init_restart_vars ==
    /\ pending_pn = [mon \in Monitors |-> 0]
    /\ pending_v = [mon \in Monitors |-> 0]
    /\ uncommitted_pn = [mon \in Monitors |-> 0]
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
    /\ step_name = "init" /\ number_crashes = 0

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Message manipulation   }\end{center}           *)
(* ^'                                                                      *)
(***************************************************************************)

(*
@typeAlias: MESSAGE = [type: MESSAGE_OP, from: MONITOR, dest: MONITOR,
                       first_committed: VALUE_VERSION, last_committed: VALUE_VERSION,
                       values: (VALUE_VERSION -> VALUE), uncommitted_pn: PN, pn: PN];
@typeAlias: MESSAGE_QUEUE = MONITOR -> (MONITOR -> Seq(MESSAGE));
*)

\* Note: Variable message_history has impact in performace, update only when debugging.

\* Converts a set with at most one element to a sequence.
\* @type: Set(MESSAGE) => Seq(MESSAGE);
SingleMessageSetToSeq(S) ==
    IF \E elem \in S: TRUE THEN LET elem == CHOOSE x \in S: TRUE
                                IN <<elem>>
                           ELSE <<>>

\* Add message m to the network msgs.
\* @type: (MESSAGE, MESSAGE_QUEUE) => MESSAGE_QUEUE;
WithMessage(m, msgs) ==
    [msgs EXCEPT ![m.from] =
        [msgs[m.from] EXCEPT ![m.dest] = Append(msgs[m.from][m.dest], m)]]

\* Remove message m from the network msgs.
\* @type: (MESSAGE, MESSAGE_QUEUE) => MESSAGE_QUEUE;
WithoutMessage(m, msgs) ==
    [msgs EXCEPT ![m.from] =
        [msgs[m.from] EXCEPT ![m.dest] = Tail(msgs[m.from][m.dest])]]

\* Adds the message m to the network.
\* Variables changed: messages, message_history.
\* @type: MESSAGE => Bool;
Send(m) ==
    /\ messages' = WithMessage(m, messages)
    \*/\ message_history' = message_history \union {m}
    /\ UNCHANGED message_history

\* Adds a set of messages to the network.
\* Variables changed: messages, message_history.
\* @type: (MONITOR, Set(MESSAGE)) => Bool;
Send_set(from, m_set) ==
    /\ messages' = [messages EXCEPT ![from] =
        [mon \in Monitors |->
            messages[from][mon] \o SingleMessageSetToSeq({m \in m_set: m.dest = mon})]]
    \*/\ message_history' = message_history \union m_set
    /\ UNCHANGED message_history

\* Removes the request from network and adds the response.
\* Variables changed: messages, message_history.
\* @type: (MESSAGE, MESSAGE) => Bool;
Reply(response, request) ==
    /\ messages' = WithoutMessage(request, WithMessage(response, messages))
    \*/\ message_history' = message_history \union {response}
    /\ UNCHANGED message_history

\* Removes the request from network and adds a set of messages.
\* Variables changed: messages, message_history.
\* @type: (MONITOR, Set(MESSAGE), MESSAGE) => Bool;
Reply_set(from, response_set, request) ==
    /\ LET msgs == WithoutMessage(request, messages)
       IN  messages' = [msgs EXCEPT ![from] =
            [mon \in Monitors |->
                msgs[from][mon] \o SingleMessageSetToSeq({m \in response_set: m.dest = mon})]]
    \*/\ message_history' = message_history \union response_set
    /\ UNCHANGED message_history

\* Removes message m from the network.
\* Variables changed: messages, message_history.
\* @type: MESSAGE => Bool;
Discard(m) ==
    /\ messages' = WithoutMessage(m, messages)
    /\ UNCHANGED message_history

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Helper predicates   }\end{center}              *)
(* ^'                                                                      *)
(***************************************************************************)

\* Computes a new unique proposal number for a given monitor.

\* Version A - Equal to the one in the source.
\* This version breaks the symmetry of the monitor set.
\* Example: oldpn = 305, rank(mon) = 5, newpn = 405.
\* @type: (MONITOR, Int) => Int;
\* get_new_proposal_number(mon, oldpn) == ((oldpn \div 100) + 1) * 100 + rank(mon)

\* Version B - Adapted to not break symmetry.
\* Example: oldpn = 300, rank(mon) = 5, newpn = 400.
\* @type: (MONITOR, Int) => Int;
get_new_proposal_number(mon, oldpn) == ((oldpn \div 100) + 1) * 100 + epoch

\* Clear the variable peer_first_committed.
\* Variables changed: peer_first_committed.
\* @type: MONITOR => Bool;
clear_peer_first_committed(mon) ==
    peer_first_committed' = [peer_first_committed EXCEPT ![mon] =
                                [m \in Monitors |-> -1]]

\* Clear the variable peer_last_committed.
\* Variables changed: peer_last_committed.
\* @type: MONITOR => Bool;
clear_peer_last_committed(mon) ==
    peer_last_committed' = [peer_last_committed EXCEPT ![mon] =
                                [m \in Monitors |-> -1]]

\* Store peer values and update first_committed, last_committed and monitor_store accordingly.
\* Variables changed: values, first_committed, last_committed, monitor_store.
\* @type: (MONITOR, MESSAGE) => Bool;
store_state(mon,msg) ==
    \* Choose peer values from mon last committed +1 to peer last committed.
    /\ LET logs == (DOMAIN msg.values) \intersect (last_committed[mon]+1..msg.last_committed)
       IN /\ values' = [values EXCEPT ![mon] =
               [i \in DOMAIN values[mon] \union logs |->
                   IF i \in logs
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
\* Variables changed: uncommitted_pn, uncommitted_v, uncommitted_value.
\* @type: MONITOR => Bool;
check_and_correct_uncommitted(mon) ==
    IF uncommitted_v[mon] <= last_committed'[mon]
    THEN /\ uncommitted_v' = [uncommitted_v EXCEPT ![mon] = 0]
         /\ uncommitted_pn' = [uncommitted_pn EXCEPT ![mon] = 0]
         /\ uncommitted_value' = [uncommitted_value EXCEPT ![mon] = Nil]
    ELSE UNCHANGED <<uncommitted_pn, uncommitted_v, uncommitted_value>>

\* Trigger new election by incrementing epoch.
\* Variables changed: epoch.
\* @type: Bool;
bootstrap ==
    /\ epoch' = epoch + 1

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Lease phase predicates   }\end{center}         *)
(* ^'                                                                      *)
(***************************************************************************)

\* Changes mon state to STATE_ACTIVE.
\* Variables changed: state.
\* @type: MONITOR => Bool;
finish_round(mon) ==
    /\ isLeader[mon] = TRUE
    /\ state' = [state EXCEPT ![mon] = STATE_ACTIVE]

\* Resets the variable acked lease and send lease messages to peers.
\* Variables changed: acked_lease, messages, message_history, phase.
\* @type: MONITOR => Bool;
extend_lease(mon) ==
    /\ isLeader[mon] = TRUE
    /\ acked_lease' = [acked_lease EXCEPT ![mon] =
        [m \in Monitors |-> IF m = mon THEN TRUE ELSE FALSE]]
    /\ Send_set(mon,
        {[type           |-> OP_LEASE,
          from           |-> mon,
          dest           |-> dest,
          last_committed |-> last_committed[mon]]: dest \in {m \in Monitors \ {mon}: quorum[m]}
         })
    /\ phase' = [phase EXCEPT ![mon] = PHASE_LEASE]

\* Handle a lease message. The peon changes his state and replies with a lease ack message.
\* The reply is commented because the lease ack is only used to check if all peers are up.
\* In the model this is done by "randomly" triggering the predicate Timeout. In this way, the search space is reduced.
\* Variables changed: messages, message_history, state.
\* @type: (MONITOR, MESSAGE) => Bool;
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
    /\ UNCHANGED <<epoch, quorum, quorum_sz, isLeader, phase>>
    /\ UNCHANGED <<restart_vars, data_vars, collect_vars, lease_vars, commit_vars>>

\* Handle a lease ack message. The leader updates the acked_lease variable.
\* Because the lease_ack messages are not sent, this predicate is never called.
\* The reasoning for this is given in handle_lease comment.
\* Variables changed: acked_lease, messages, message_history.
\* @type: (MONITOR, MESSAGE) => Bool;
handle_lease_ack(mon, msg) ==
    /\ phase[mon] = PHASE_LEASE
    /\ acked_lease' = [acked_lease EXCEPT ![mon] =
        [acked_lease[mon] EXCEPT ![msg.from] = TRUE]]
    /\ Discard(msg)
    /\ UNCHANGED <<epoch, quorum, quorum_sz>>
    /\ UNCHANGED <<state_vars, restart_vars, data_vars, collect_vars, commit_vars>>

\* Predicate that is called when all peers ack the lease. The phase is changed to prevent loops.
\* Because the lease_ack messages are not sent, this predicate is never called.
\* The reasoning for this is given in handle_lease comment.
\* Variables changed: phase.
\* @type: MONITOR => Bool;
post_lease_ack(mon) ==
    /\ phase[mon] = PHASE_LEASE
    /\ phase' = [phase EXCEPT ![mon] = PHASE_LEASE_DONE]
    /\ \A m \in Monitors: quorum[m] => acked_lease[mon][m] = TRUE
    /\ UNCHANGED <<isLeader, state>>
    /\ UNCHANGED <<global_vars, restart_vars, data_vars, collect_vars,
                   lease_vars, commit_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Commit phase predicates   }\end{center}        *)
(* ^'                                                                      *)
(***************************************************************************)

\* Start a commit phase by the leader. The variable new_value is assigned. Send begin messages to the peers.
\* The new value is stored in values and pending_pn is assigned in order for the leader to be
\* able to recover from a crash.
\* Variables changed: accepted, new_value, phase, messages, message_history, values, pending_pn, pending_v.
\* @type: (MONITOR, VALUE) => Bool;
begin(mon, v) ==
    /\ isLeader[mon] = TRUE
    /\ \/ state'[mon] = STATE_UPDATING
       \/ state'[mon] = STATE_UPDATING_PREVIOUS
    /\ quorum_sz = 1 \/ num_last[mon] > MonitorsLen \div 2
    /\ new_value[mon] = Nil
    /\ accepted' = [accepted EXCEPT ![mon] =
        [m \in Monitors |-> IF m = mon THEN TRUE ELSE FALSE]]
    /\ new_value' = [new_value EXCEPT ![mon] = v]
    /\ phase' = [phase EXCEPT ![mon] = PHASE_BEGIN]
    /\ values' = [values EXCEPT ![mon] =
        ((last_committed[mon] + 1) :> new_value'[mon]) @@ values[mon] ]
    /\ Send_set(mon,
        {[type           |-> OP_BEGIN,
          from           |-> mon,
          dest           |-> dest,
          last_committed |-> last_committed[mon],
          values         |-> values'[mon],
          pn             |-> accepted_pn[mon]]: dest \in {m \in Monitors \ {mon}: quorum[m]}
         })
    /\ pending_pn' = [pending_pn EXCEPT ![mon] = accepted_pn[mon]]
    /\ pending_v' = [pending_v EXCEPT ![mon] = last_committed[mon]+1]

\* Handle a begin message. The monitor will accept if the proposal number in the message is greater
\* or equal than the one he accepted.
\* Similar to what happens in begin, values and pending_pn are assigned in order for
\* the monitor to recover in case of a crash.
\* Variables changed: messages, message_history, state, values, pending_pn, pending_v.
\* @type: (MONITOR, MESSAGE) => Bool;
handle_begin(mon, msg) ==
    /\ isLeader[mon] = FALSE
    /\ IF msg.pn < accepted_pn[mon]
       THEN
        /\ Discard(msg)
        /\ UNCHANGED <<state, values, pending_pn, pending_v>>
       ELSE
        /\ msg.pn = accepted_pn[mon]
        /\ msg.last_committed = last_committed[mon]

        \* assign values[mon][last_committed[mon]+1]
        /\ values' = [values EXCEPT ![mon] =
            ((last_committed[mon] + 1) :> msg.values[last_committed[mon] + 1]) @@ values[mon] ]

        /\ state' = [state EXCEPT ![mon] = STATE_UPDATING]
        /\ pending_pn' = [pending_pn EXCEPT ![mon] = accepted_pn[mon]]
        /\ pending_v' = [pending_v EXCEPT ![mon] = last_committed[mon]+1]
        /\ Reply([type            |-> OP_ACCEPT,
                  from            |-> mon,
                  dest            |-> msg.from,
                  last_committed  |-> last_committed[mon],
                  pn              |-> accepted_pn[mon]],msg)
    /\ UNCHANGED <<epoch, quorum, quorum_sz, isLeader, phase, monitor_store,
                   accepted_pn, first_committed, last_committed, uncommitted_pn,
                   uncommitted_v, uncommitted_value>>
    /\ UNCHANGED <<collect_vars, lease_vars, commit_vars>>

\* Handle an accept message. If the leader receives a positive response from the peer, it will
\* add it to the variable accepted.
\* Variables changed: messages, message_history, accepted
\* @type: (MONITOR, MESSAGE) => Bool;
handle_accept(mon, msg) ==
    /\ isLeader[mon] = TRUE
    /\ \/ state[mon] = STATE_UPDATING_PREVIOUS
       \/ state[mon] = STATE_UPDATING
    /\ phase[mon] = PHASE_BEGIN
    /\ new_value[mon] # Nil
    /\ IF \/ msg.pn # accepted_pn[mon]
          \/ /\ last_committed[mon] > 0
             /\ msg.last_committed < last_committed[mon]-1
       THEN UNCHANGED accepted
       ELSE accepted' = [accepted EXCEPT ![mon] =
                [accepted[mon] EXCEPT ![msg.from] = TRUE]]
    /\ Discard(msg)
    /\ UNCHANGED <<epoch, quorum, quorum_sz, pending_proposal, new_value>>
    /\ UNCHANGED <<restart_vars, state_vars, data_vars, collect_vars, lease_vars>>

\* Predicate that is enabled and called when all peers in the quorum accept begin request from leader.
\* The leader commits the transaction in new_value and sends commit messages to his peers.
\* Variables changed: first_committed, last_committed, monitor_store, new_value, messages, message_history, state, phase
\* @type: MONITOR => Bool;
post_accept(mon) ==
    /\ phase[mon] = PHASE_BEGIN
    /\ \A m \in Monitors: quorum[m] => accepted[mon][m] = TRUE
    /\ new_value[mon] # Nil
    /\ \/ state[mon] = STATE_UPDATING_PREVIOUS
       \/ state[mon] = STATE_UPDATING
    /\ last_committed' = [last_committed EXCEPT ![mon] = last_committed[mon] + 1]

    /\ IF first_committed[mon] = 0
       THEN first_committed' = [first_committed EXCEPT ![mon] = first_committed[mon] + 1]
       ELSE UNCHANGED first_committed

    /\ monitor_store' = [monitor_store EXCEPT ![mon] = values[mon][last_committed[mon]+1]]
    /\ new_value' = [new_value EXCEPT ![mon] = Nil]
    /\ Send_set(mon,
        {[type           |-> OP_COMMIT,
          from           |-> mon,
          dest           |-> dest,
          last_committed |-> last_committed'[mon],
          pn             |-> accepted_pn[mon],
          values         |-> values[mon]]: dest \in {m \in Monitors \ {mon}: quorum[m]}
         })
    /\ state' = [state EXCEPT ![mon] = STATE_REFRESH]
    /\ phase' = [phase EXCEPT ![mon] = PHASE_COMMIT]
    /\ UNCHANGED <<isLeader, values, accepted_pn, pending_proposal, accepted>>
    /\ UNCHANGED <<epoch, quorum, quorum_sz, restart_vars, collect_vars, lease_vars>>

\* Predicate that is called after post_accept. The leader finishes the commit phase by updating his state to
\* STATE_ACTIVE and by extending the lease to his peers.
\* Variables changed: state, phase, acked_lease, messages, message_history.
\* @type: MONITOR => Bool;
finish_commit(mon) ==
    /\ state[mon] = STATE_REFRESH
    /\ phase[mon] = PHASE_COMMIT
    /\ finish_round(mon)
    /\ extend_lease(mon)
    /\ UNCHANGED <<epoch, quorum, quorum_sz, isLeader>>
    /\ UNCHANGED <<restart_vars, data_vars, collect_vars, commit_vars>>

\* Handle a commit message. The monitor stores the values sent by the leader commit message.
\* Variables changed: messages, message_history, values, first_committed, last_committed, monitor_store, uncommitted_v,
\* uncommitted_pn, uncommitted_value.
\* @type: (MONITOR, MESSAGE) => Bool;
handle_commit(mon, msg) ==
    /\ isLeader[mon] = FALSE
    /\ store_state(mon, msg)
    /\ check_and_correct_uncommitted(mon)
    /\ Discard(msg)
    /\ UNCHANGED <<epoch, quorum, quorum_sz, accepted_pn, pending_pn, pending_v>>
    /\ UNCHANGED <<state_vars, collect_vars, lease_vars, commit_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Client Request   }\end{center}                 *)
(* ^'                                                                      *)
(***************************************************************************)

\* Request a transaction v to the monitor. The transaction is saved on pending proposal to be committed in
\* the next available commit phase.
\* Variables changed: pending_proposal.
\* @type: (MONITOR, VALUE) => Bool;
client_request(mon, v) ==
    /\ isLeader[mon] = TRUE
    /\ state[mon] = STATE_ACTIVE
    /\ pending_proposal[mon] = Nil
    /\ pending_proposal' = [pending_proposal EXCEPT ![mon] = v]
    /\ UNCHANGED <<new_value, accepted>>
    /\ UNCHANGED <<global_vars, state_vars, restart_vars, data_vars, collect_vars, lease_vars>>

\* Start a commit phase with the value on pending proposal.
\* Variables changed: state, pending_proposal, accepted, new_value, phase, messages, message_history, values,
\* pending_pn, pending_v.
\* @type: MONITOR => Bool;
propose_pending(mon) ==
    /\ phase[mon] = PHASE_LEASE \/ phase[mon] = PHASE_ELECTION
    /\ state[mon] = STATE_ACTIVE
    /\ pending_proposal[mon] # Nil
    /\ pending_proposal' = [pending_proposal EXCEPT ![mon] = Nil]
    /\ state' = [state EXCEPT ![mon] = STATE_UPDATING]
    /\ begin(mon, pending_proposal[mon])
    /\ UNCHANGED <<isLeader, monitor_store, accepted_pn, first_committed, last_committed,
                   epoch, quorum, quorum_sz, uncommitted_v, uncommitted_pn, uncommitted_value>>
    /\ UNCHANGED <<collect_vars, lease_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Collect phase predicates   }\end{center}       *)
(* ^'                                                                      *)
(***************************************************************************)

\* Start collect phase. This first part of the collect phase is divided in two parts (collect and send_collect)
\* in order to simplify variable changes (when collect is triggered from handle_last).
\* Variables changed: accepted_pn, phase.
\* @type: (MONITOR, Int) => Bool;
collect(mon, oldpn) ==
    /\ state[mon] = STATE_RECOVERING
    /\ isLeader[mon] = TRUE
    /\ LET new_pn == get_new_proposal_number(mon, Max({oldpn,accepted_pn[mon]}))
       IN  /\ accepted_pn' = [accepted_pn EXCEPT ![mon] = new_pn]
    /\ phase' = [phase EXCEPT ![mon] = PHASE_SEND_COLLECT]

\* Continue the start of the collect phase. Initialize the number of peers that accepted the proposal (num_last) and
\* the variables with peers version numbers. Check if there is an uncommitted value.
\* Send collect messages to the peers.
\* Variables changed: peer_first_committed, peer_last_committed, uncommitted_pn, uncommitted_v, uncommitted_value, num_last,
\* messages, message_history, phase.
\* @type: MONITOR => Bool;
send_collect(mon) ==
    /\ state[mon] = STATE_RECOVERING
    /\ isLeader[mon] = TRUE
    /\ phase[mon] = PHASE_SEND_COLLECT
    /\ clear_peer_first_committed(mon)
    /\ clear_peer_last_committed(mon)

    /\ IF last_committed[mon]+1 \in DOMAIN values[mon]
       THEN /\ uncommitted_v' =
                [uncommitted_v EXCEPT ![mon] = last_committed[mon]+1]
            /\ uncommitted_value' =
                [uncommitted_value EXCEPT ![mon] = values[mon][last_committed[mon]+1]]
            /\ uncommitted_pn' = [uncommitted_pn EXCEPT ![mon] = pending_pn[mon]]
            /\ UNCHANGED <<pending_pn, pending_v>>
       ELSE UNCHANGED <<restart_vars>>

    /\ num_last' = [num_last EXCEPT ![mon] = 1]
    /\ Send_set(mon,
        {[type            |-> OP_COLLECT,
          from            |-> mon,
          dest            |-> dest,
          first_committed |-> first_committed[mon],
          last_committed  |-> last_committed[mon],
          pn              |-> accepted_pn[mon]]: dest \in {m \in Monitors \ {mon}: quorum[m]}
         })
    /\ phase' = [phase EXCEPT ![mon] = PHASE_COLLECT]
    /\ UNCHANGED <<isLeader, state>>
    /\ UNCHANGED <<epoch, quorum, quorum_sz, data_vars, lease_vars, commit_vars>>

\* Handle a collect message. The peer will accept the proposal number from the leader if it is bigger than the last
\* proposal number he accepted.
\* Variables changed: messages, message_history, epoch, state, accepted_pn.
\* @type: (MONITOR, MESSAGE) => Bool;
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
                    uncommitted_pn  |-> pending_pn[mon],
                    pn              |-> accepted_pn'[mon]],msg)
          /\ UNCHANGED epoch
    /\ UNCHANGED <<isLeader, phase, values, first_committed, last_committed, monitor_store>>
    /\ UNCHANGED <<quorum, quorum_sz, restart_vars, collect_vars, lease_vars, commit_vars>>

\* Handle a last message (response from a peer to the leader collect message).
\* The peers first and last committed version are stored. If the leader is behind, bootstraps. Stores any value that
\* the peer may have committed (store_state). If peer is behind send commit message with leader values.
\* If peer accepted proposal number increase num last, if he sent a bigger proposal number start a new collect phase.
\* Variables changed: messages, message_history, epoch, phase, uncommitted_pn, uncommitted_v, uncommitted_value, monitor_store, values,
\* accepted_pn, first_committed, last_committed, num_last, peer_first_committed, peer_last_committed.
\* @type: (MONITOR, MESSAGE) => Bool;
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
        /\ UNCHANGED <<first_committed, last_committed, uncommitted_pn, uncommitted_v, uncommitted_value>>
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
                    /\ peer_last_committed'[mon][peer] < last_committed[mon]
                    /\ quorum[peer]}
               IN Reply_set(mon,
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
                        /\ msg.uncommitted_pn >= uncommitted_pn[mon]
                     THEN /\ uncommitted_v' =
                                [uncommitted_v EXCEPT ![mon] = msg.last_committed+1]
                          /\ uncommitted_pn' =
                                [uncommitted_pn EXCEPT ![mon] = msg.uncommitted_pn]
                          /\ uncommitted_value' =
                                [uncommitted_value EXCEPT ![mon] = msg.values[msg.last_committed+1]]
                     ELSE check_and_correct_uncommitted(mon)
                  /\ UNCHANGED <<phase, accepted_pn>>

               \/ /\ msg.pn < accepted_pn[mon]
                  /\ check_and_correct_uncommitted(mon)
                  /\ UNCHANGED <<phase, accepted_pn, num_last>>
            /\ UNCHANGED epoch
       /\ UNCHANGED epoch

    /\ UNCHANGED <<quorum, quorum_sz, isLeader, state, pending_pn, pending_v>>
    /\ UNCHANGED <<lease_vars, commit_vars>>

\* Predicate that is enabled and called when all peers in quorum accept collect request from leader. If there is an
\* uncommitted value, a commit phase is started with that value, else the leader changes to ACTIVE_STATE and extends
\* the lease to his peers.
\* Variables changed: peer_first_committed, peer_last_committed, state, accepted, new_value, phase, messages,
\* message_history, values, pending_pn, pending_v, acked_lease.
\* @type: MONITOR => Bool;
post_last(mon) ==
    /\ isLeader[mon] = TRUE
    /\ num_last[mon] = quorum_sz
    /\ phase[mon] = PHASE_COLLECT

    /\ clear_peer_first_committed(mon)
    /\ clear_peer_last_committed(mon)

    /\ IF /\ uncommitted_v[mon] = last_committed[mon]+1
          /\ uncommitted_value[mon] # Nil
       THEN /\ state' = [state EXCEPT ![mon] = STATE_UPDATING_PREVIOUS]
            /\ begin(mon, uncommitted_value[mon])
            /\ UNCHANGED <<acked_lease, uncommitted_v, uncommitted_pn, uncommitted_value>>
       ELSE /\ finish_round(mon)
            /\ extend_lease(mon)
            /\ UNCHANGED <<accepted, new_value, values, restart_vars>>

    /\ UNCHANGED <<isLeader, monitor_store, accepted_pn, first_committed, last_committed>>
    /\ UNCHANGED <<epoch, quorum, quorum_sz, num_last, pending_proposal>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Leader election   }\end{center}                *)
(* ^'                                                                      *)
(***************************************************************************)

\* Elect one monitor as a leader and initialize the remaining ones as peons.
\* Variables changed: isLeader, state, phase, new_value, pending_proposal, epoch.
\* @type: Bool;
leader_election ==
    /\ \E mon \in Monitors:
        /\ quorum[mon]
        /\ isLeader' = [m \in Monitors |-> IF m = mon THEN TRUE ELSE FALSE]
        /\ state' = [m \in Monitors |->
            IF quorum_sz = 1 THEN STATE_ACTIVE ELSE STATE_RECOVERING]
    /\ phase' = [m \in Monitors |-> PHASE_ELECTION]
    /\ new_value' = [m \in Monitors |-> Nil]
    /\ pending_proposal' = [m \in Monitors |-> Nil]
    /\ epoch' = epoch + 1
    /\ messages' = [mon1 \in Monitors |-> [mon2 \in Monitors |-> <<>>] ]
    /\ UNCHANGED <<quorum, quorum_sz, accepted, message_history>>
    /\ UNCHANGED <<data_vars, restart_vars, collect_vars, lease_vars>>

\* Start recovery phase if number of monitors in quorum is greater than 1.
\* Variables changed: accepted_pn, phase.
\* @type: MONITOR => Bool;
election_recover(mon) ==
    /\ quorum_sz > 1
    /\ phase[mon] = PHASE_ELECTION
    /\ collect(mon,0)
    /\ UNCHANGED <<isLeader, state, values, first_committed, last_committed, monitor_store>>
    /\ UNCHANGED <<global_vars, restart_vars, collect_vars, lease_vars, commit_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Timeouts and restart   }\end{center}           *)
(* ^'                                                                      *)
(***************************************************************************)
\* Remove monitor from quorum, if there are enough monitors in the quorum.
\* @type: MONITOR => Bool;
crash_mon(mon) ==
    /\ quorum_sz > (MonitorsLen \div 2) + 1
    /\ quorum[mon] = TRUE
    /\ quorum' = [quorum EXCEPT ![mon] = FALSE]
    /\ quorum_sz' = quorum_sz - 1
    /\ bootstrap
    \*/\ number_crashes' = number_crashes+1
    /\ UNCHANGED <<messages, message_history>>
    /\ UNCHANGED <<state_vars, restart_vars, data_vars, collect_vars, lease_vars, commit_vars>>

\* Add monitor to the quorum.
\* @type: MONITOR => Bool;
restore_mon(mon) ==
    /\ quorum[mon] = FALSE
    /\ quorum' = [quorum EXCEPT ![mon] = TRUE]
    /\ quorum_sz' = quorum_sz + 1
    /\ bootstrap
    /\ UNCHANGED <<messages, message_history>>
    /\ UNCHANGED <<state_vars, restart_vars, data_vars, collect_vars, lease_vars, commit_vars>>

\* Monitor timeout (simulate the various timeouts that can occur). Triggers new elections.
\* Variables changed: epoch.
\* @type: MONITOR => Bool;
Timeout(mon) ==
    /\ bootstrap
    /\ UNCHANGED <<messages, quorum, quorum_sz, message_history, state_vars, restart_vars,
                   data_vars, collect_vars, lease_vars, commit_vars>>

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Dispatchers and next statement   }\end{center} *)
(* ^'                                                                      *)
(***************************************************************************)

\* Handle a message.
\* @type: MESSAGE => Bool;
Receive(msg) ==
    /\ \/ /\ msg.type = OP_COLLECT
          /\ handle_collect(msg.dest, msg)
          /\ step_name' = "receive collect"

       \/ /\ msg.type = OP_LAST
          /\ handle_last(msg.dest, msg)
          /\ step_name' = "receive last"

       \/ /\ msg.type = OP_LEASE
          /\ handle_lease(msg.dest, msg)
          /\ step_name' = "receive lease"

       \/ /\ msg.type = OP_LEASE_ACK
          /\ handle_lease_ack(msg.dest, msg)
          /\ step_name' = "receive lease_ack"

       \/ /\ msg.type = OP_BEGIN
          /\ handle_begin(msg.dest, msg)
          /\ step_name' = "receive begin"

       \/ /\ msg.type = OP_ACCEPT
          /\ handle_accept(msg.dest, msg)
          /\ step_name' = "receive accept"

       \/ /\ msg.type = OP_COMMIT
          /\ handle_commit(msg.dest, msg)
          /\ step_name' = "receive commit"

\* Limit some variables to reduce search space.
\* @type: Bool;
reduce_search_space ==
    /\ epoch # 8
    /\ \/ \A mon \in Monitors: last_committed[mon] < 2
       \*\/ \A mon2 \in Monitors: new_value[mon2] = Nil
    /\ \A mon \in Monitors: accepted_pn[mon] < 300
    \*/\ number_crashes # 4

\* State transitions.
\* @type: Bool;
Next ==
    /\ reduce_search_space
    /\ IF epoch % 2 = 1 THEN
        /\ leader_election
        /\ step_name' = "election"
        /\ UNCHANGED number_crashes
       ELSE
        \/ /\ \E mon \in Monitors: election_recover(mon)
           /\ step_name' = "election_recover"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: send_collect(mon)
           /\ step_name' = "send_collect"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: post_last(mon)
           /\ step_name' = "post_last"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: post_lease_ack(mon)
           /\ step_name' = "post_lease_ack"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: post_accept(mon)
           /\ step_name' = "post_accept"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: finish_commit(mon)
           /\ step_name' = "finish_commit"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: \E v \in Value_set: client_request(mon, v)
           /\ step_name' = "client_request"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: propose_pending(mon)
           /\ step_name' = "propose_pending"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon1, mon2 \in Monitors:
                /\ mon1 # mon2
                /\ Len(messages[mon1][mon2])>0
                /\ Receive(messages[mon1][mon2][1])
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: crash_mon(mon)
           /\ step_name' = "crash_mon"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: restore_mon(mon)
           /\ step_name' = "restore_mon"
           /\ UNCHANGED number_crashes

        \/ /\ \E mon \in Monitors: Timeout(mon)
           /\ step_name' = "timeout_and_restart"
           /\ UNCHANGED number_crashes

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Safety invariants   }\end{center}              *)
(* ^'                                                                      *)
(***************************************************************************)

\* If two monitors are in state active then their monitor_store must have the same value.
\* @type: Bool;
same_monitor_store == \A mon1, mon2 \in Monitors:
    state[mon1] = STATE_ACTIVE /\ state[mon2] = STATE_ACTIVE
    => monitor_store[mon1] = monitor_store[mon2]

\* Invariant.
\* @type: Bool;
Inv == /\ same_monitor_store

(***************************************************************************)
(* `^                                                                      *)
(* \begin{center}\textbf{   Test/Debug invariants   }\end{center}          *)
(* ^'                                                                      *)
(***************************************************************************)

\* Invariant used to search for a state where 'x' happens.
Inv_find_state(x) == ~x

\* Invariant used to search for a behavior of diameter equal to 'size'.
\* TLCGet("level") not supported by snowcat typechecker.
\* Inv_diam(size) == TLCGet("level") # size-1

\* Invariants to test in model check
DEBUG_Inv == /\ TRUE
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
    /\ step_name="crash mon"

    \* The system is in collect phase and no OP_LAST message has been received.
    \* isLeader[mon] = TRUE assures that the leader was not the one that crashed.
    /\ \E mon \in Monitors:
        /\ isLeader[mon] = TRUE
        /\ phase[mon] = PHASE_COLLECT
        /\ num_last[mon] = 1

    \* All the collect requests have been handled by the peers.
    /\ \A mon1, mon2 \in Monitors:
        \A i \in 1..Len(messages[mon1][mon2]): messages[mon1][mon2][i].type # OP_COLLECT

    /\ epoch = 2
)

Find a state where the leader crashes during the commit phase, failing to complete the commit.
Inv_find_state(
    /\ step_name="crash mon"
    /\ \E mon1, mon2 \in Monitors:
        \E i \in 1..Len(messages[mon1][mon2]): messages[mon1][mon2][i].type = OP_ACCEPT
    /\ \A mon \in Monitors:
        isLeader[mon] = FALSE
    /\ epoch = 2
)
Note: After finding a state, that complete state can be used as an initial state to analyze behaviors from there.
*)

=============================================================================
\* Modification History
\* Last modified Sun Apr 18 22:54:31 WEST 2021 by afonsonf
\* Created Mon Jan 11 16:15:26 WET 2021 by afonsonf
