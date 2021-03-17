## Description of the specification

### Specification overview

The system starts in an initial configuration where each variable has an initial value assigned.

From the initial configuration the system can take a set of transitions that will define how a variable can change.
The variable epoch defines if the system is or is not in an election phase (epoch%2 = 1 means it is in an election).

The election is done randomly, and for now, only one leader is chosen.
After election, if the number of monitors is bigger than one, the system enters a recovery phase where the leader will try to synchronize its values with his peers and agree on a proposal number.

When a proposal number is agreed on, if the leader has an uncommitted value it will start an updating phase to try to commit the value, else it will change to active state and wait for client requests.

If the leader changes to an active state it will tell its peers, allowing them to change also to an active state (extend lease).

The commit phase starts by first sharing the value to be committed and asking his peers if it is OK to commit (ask if leader has correct proposal number and log). If the leader receives enough positive responses from his peers it will send a message to allow the peers to commit.

### Overview of some mechanisms in the specification

The specification is written to mirror what is implemented in Ceph (source file: https://github.com/ceph/ceph/blob/master/src/mon/Paxos.cc). However, the algorithm implemented depends on other modules, such as election logic and the network layer.

These modules are abstracted in the specification to have the same behaviour. The main mechanism abstracted are:

* Election logic. The leader is chosen randomly and, for now, only one per epoch. When a new epoch begins, the messages from the previous epoch are discarded.
* Monitor quorum. The quorum is defined in the election phase, using all monitors that are up. Different epochs can have different quorums.
* The communication layer. The variable messages represents connections between monitors (e.g. messages\[mon1\]\[mon2\] holds the messages sent from mon1 to mon2). Within a connection the messages are sent and received in order.
* The transactions. Transactions are simplified to represent only a change of a value in the variable monitor_store.
* Failure model. A monitor can crash if the remaining number of monitors is sufficient to form a quorum. When a monitor crashes, new elections are triggered and the monitor is marked to not be part of the quorum until he recovers.
* Timeouts. A timeout can occur at any point in the algorithm and it will trigger new elections.

### Specification structure

The specification file is divided in the following sections:

* Constants. Declaration of constants such as the set of ids for the monitors and the state names and messages types.
* Declaration of variables, divided in sections depending on which phases of the algorithm they are used.
* Message manipulation. Functions for network manipulation (adding and removing messages from the network).
* Helper predicates.
* Lease phase predicates. Functions to send and handle lease type messages and start a lease phase.
* Commit phase predicates. Functions used in the commit phase, responsible for applying new transactions in all the quorum.
* Client Request. Functions to add pending proposal to the leader and start commit phase with them.
* Collect phase predicates. Functions used in the collect phase, responsible for recovery of the quorum and agreement on a new proposal number.
* Leader election. Functions to select a new leader and, if the number of monitors if bigger than one, start a collect phase.
* Dispatchers and next statement. Definition of the possible transitions between states.

### Change of state variables between transitions

The functions described in the specification are not all called in the start of a transition. For example the collect function (to start a collect phase), can only be called following the state transition of a leader election or handling a OP_LAST message.<br>
In this section is described how some of the state variables change between state transition functions. <br>

* leader_election: (system) <br>
  state, _ -> STATE_ACTIVE | STATE_RECOVERING <br>
  phase, _ -> PHASE_ELECTION <br>

* election_recover: (leader) <br>
  state, STATE_RECOVERING <br>
  phase, PHASE_ELECTION -> PHASE_SEND_COLLECT <br>

* pre_send_collect: (leader) <br>
  state, STATE_RECOVERING <br>
  phase, PHASE_SEND_COLLECT -> PHASE_COLLECT <br>

* handle_collect: (peon) <br>
  state, _ -> STATE_RECOVERING <br>
  phase, _ <br>

* handle_last: (leader) <br>
  state, STATE_RECOVERING <br>
  phase, PHASE_COLLECT -> PHASE_SEND_COLLECT | PHASE_COLLECT <br>

* post_last: (leader) <br>
  state, STATE_RECOVERING -> STATE_UPDATING_PREVIOUS | STATE_ACTIVE <br>
  phase, PHASE_COLLECT -> PHASE_BEGIN | PHASE_LEASE <br>

* client_request: (leader) <br>
  state, STATE_ACTIVE <br>
  phase, PHASE_LEASE | PHASE_ELECTION <br>

* propose_pending: (leader) <br>
  state, STATE_ACTIVE -> STATE_UPDATING <br>
  phase, PHASE_LEASE | PHASE_ELECTION -> PHASE_BEGIN <br>

* handle_begin: (peon) <br>
  state, _ -> STATE_UPDATING <br>
  phase, _ <br>

* handle_accept: (leader) <br>
  state, STATE_UPDATING_PREVIOUS | STATE_UPDATING <br>
  phase, PHASE_BEGIN <br>

* post_accept: (leader) <br>
  state, STATE_UPDATING_PREVIOUS | STATE_UPDATING -> STATE_REFRESH <br>
  phase, PHASE_BEGIN -> PHASE_COMMIT <br>

* finish_commit: (leader)
  state, STATE_REFRESH -> STATE_ACTIVE <br>
  phase, PHASE_COMMIT -> PHASE_LEASE <br>

* handle_commit: (peon) <br>
  state, _ <br>
  phase, _ <br>

* handle_lease: (peon) <br>
  state, _ -> STATE_ACTIVE <br>
  phase, _ <br>

* handle_lease_ack: (leader) <br>
  state, _ <br>
  phase, PHASE_LEASE <br>

* post_lease_ack: (leader) <br>
  state, _ <br>
  phase, PHASE_LEASE -> PHASE_LEASE_DONE <br>
