----------------------- MODULE CheckpointCoordination -----------------------
EXTENDS
  Naturals,
  FiniteSets,
  Sequences

CONSTANTS 
  Node,           \* The set of all nodes available for use in the cluster
  Majority        \* The number of nodes constituting a majority

VARIABLES
  IsNodeUp,           \* Whether each node is up
  NetworkPath,        \* Whether a network path exists between nodes
  Leader,             \* Which node is currently elected leader
  ReplicatedLog,      \* The replicated log of commands on each node
  ExecutionCounter,   \* The index in the log each node will next execute
  LastVotePayload,    \* Data field which piggybacks on vote responses
  CurrentLease,       \* The current checkpoint lease recorded at each nodes
  CanTakeCheckpoint,  \* Whether node believes it can take a checkpoint
  IsTakingCheckpoint, \* Whether node is currently taking a checkpoint
  TimeoutCounter,     \* Counter of oldest lease which has not yet timed out
  LatestCheckpoint    \* The latest recorded log checkpoint

(***************************************************************************)
(* Variables relating to the environment in which the cluster is running.  *)
(***************************************************************************)
EnvironmentVars == <<
  IsNodeUp,
  NetworkPath
>>

(***************************************************************************)
(* Variables relating to the function of the Paxos (RSL) system itself.    *)
(***************************************************************************)
PaxosVars == <<
  Leader,
  ReplicatedLog,
  ExecutionCounter,
  LastVotePayload
>>

(***************************************************************************)
(* Variables relating to the checkpoint coordination system logic.         *)
(***************************************************************************)
CheckpointVars == <<
  CurrentLease,
  CanTakeCheckpoint,
  IsTakingCheckpoint,
  TimeoutCounter,
  LatestCheckpoint
>>

(***************************************************************************)
(* All variables.                                                          *)
(***************************************************************************)
AllVars == <<
  IsNodeUp,
  NetworkPath,
  Leader,
  ReplicatedLog,
  ExecutionCounter,
  LastVotePayload,
  CurrentLease,
  CanTakeCheckpoint,
  IsTakingCheckpoint,
  TimeoutCounter,
  LatestCheckpoint
>>

(***************************************************************************)
(* An arbitrary value not in the set of all nodes.                         *)
(***************************************************************************)
NoNode == CHOOSE n : n \notin Node

(***************************************************************************)
(* The set of all logs, the values of which are decided by Paxos.          *)
(***************************************************************************)
Log == Seq(Node \cup {NoNode})

(***************************************************************************)
(* The set of all log indices.                                             *)
(***************************************************************************)
LogIndex == Nat \ {0}

(***************************************************************************)
(* The very first log index.                                               *)
(***************************************************************************)
MinLogIndex == 1

(***************************************************************************)
(* A blank log.                                                            *)
(***************************************************************************)
BlankLog == [i \in LogIndex |-> NoNode]

(***************************************************************************)
(* The set of all log checkpoints.                                         *)
(***************************************************************************)
LogCheckpoint == [
  log     : Log,      \* The saved log entries
  counter : LogIndex  \* Highest log index in checkpoint, exclusive
]

(***************************************************************************)
(* The set of all log checkpoint leases.                                   *)
(***************************************************************************)
CheckpointLease == [
  node    : Node,     \* The node to which the checkpoint lease applies
  counter : LogIndex  \* The log index at which the lease was issued
]

(***************************************************************************)
(* Value indicating no checkpoint lease.                                   *)
(***************************************************************************)
NoCheckpointLease == CHOOSE lease : lease \notin CheckpointLease

(***************************************************************************)
(* Reads the value from the index of the node's log.                       *)
(***************************************************************************)
ReadLog(node, index) ==
  IF index \in DOMAIN ReplicatedLog[node]
  THEN ReplicatedLog[node][index]
  ELSE NoNode

(***************************************************************************)
(* Writes the value to the index of the node's log.                        *)
(***************************************************************************)
WriteLog(node, index, value) == [
  [i \in LogIndex |-> ReadLog(node, i)] EXCEPT ![index] = value
]

(***************************************************************************)
(* Merges the logs of two replicas. Replica logs can differ if one was     *)
(* unable to receive messages from the leader. While replica logs can be   *)
(* missing values, they will never have conflicting values for any index.  *)
(***************************************************************************)
MergeLogs(srcNode, dstNode) == [
  i \in LogIndex |->
    IF ReadLog(dstNode, i) /= NoNode
    THEN ReadLog(dstNode, i)
    ELSE ReadLog(srcNode, i)
]

(***************************************************************************)
(* The set of all unused log indices.                                      *)
(***************************************************************************)
OpenIndices == {
  i \in LogIndex :
    \A n \in Node :
      ReadLog(n, i) = NoNode
}

(***************************************************************************)
(* Finds the first unused replicated log index.                            *)
(***************************************************************************)
FirstOpenIndex ==
  CHOOSE index \in OpenIndices :
    \A other \in OpenIndices :
      index <= other

(***************************************************************************)
(* The type invariant of all variables.                                    *)
(***************************************************************************)
TypeInvariant ==
  /\ IsNodeUp \in [Node -> BOOLEAN]
  /\ NetworkPath \in [Node \X Node -> BOOLEAN]
  /\ Leader \in Node \cup {NoNode}
  /\ ReplicatedLog \in [Node -> Log]
  /\ ExecutionCounter \in [Node -> LogIndex]
  /\ LastVotePayload \in [Node -> LogIndex]
  /\ CurrentLease \in [Node -> (CheckpointLease \cup {NoCheckpointLease})]
  /\ CanTakeCheckpoint \in [Node -> BOOLEAN]
  /\ IsTakingCheckpoint \in [Node -> BOOLEAN]
  /\ TimeoutCounter \in LogIndex
  /\ LatestCheckpoint \in LogCheckpoint

(***************************************************************************)
(* Safety checks which must hold in all states for the system to be        *)
(* considered functional.                                                  *)
(***************************************************************************)
SafetyInvariant ==
  /\ Leader /= NoNode =>
    \* The leader cannot take a checkpoint
    /\ ~CanTakeCheckpoint[Leader]
    /\ ~IsTakingCheckpoint[Leader]
    \* If the leader doesn't know about a lease, neither does any node
    /\ CurrentLease[Leader] = NoCheckpointLease =>
      /\ \A n \in Node :
        /\ ~CanTakeCheckpoint[n]
        /\ ~IsTakingCheckpoint[n]
    \* If the leader knows about a lease, only that node can checkpoint
    /\ CurrentLease[Leader] /= NoCheckpointLease =>
      /\ \A n \in Node :
        /\ (CanTakeCheckpoint[n] \/ IsTakingCheckpoint[n]) =>
          /\ CurrentLease[Leader].node = n
  \* Two nodes can't take a checkpoint simultaneously
  /\ \A n1, n2 \in Node :
    /\ (CanTakeCheckpoint[n1] /\ CanTakeCheckpoint[n2]) =>
      /\ n1 = n2
    /\ (IsTakingCheckpoint[n1] /\ IsTakingCheckpoint[n2]) =>
      /\ n1 = n2
  \* Prerequisites for taking a checkpoint must be satisfied
  /\ \A n \in Node :
    /\ IsTakingCheckpoint[n] => CanTakeCheckpoint[n]
    /\ CanTakeCheckpoint[n] => (CurrentLease[n] /= NoCheckpointLease)
    /\ CanTakeCheckpoint[n] => CurrentLease[n].node = n
    /\ CanTakeCheckpoint[n] => CurrentLease[n].counter >= TimeoutCounter
  \* Replicated logs can never conflict
  /\ \A i \in LogIndex :
    /\ \A n1, n2 \in Node :
      \/ ReadLog(n1, i) = NoNode
      \/ ReadLog(n2, i) = NoNode
      \/ ReadLog(n1, i) = ReadLog(n2, i)

(***************************************************************************)
(* Expectations about system capabilities.                                 *)
(***************************************************************************)
TemporalInvariant ==
  \* Eventually, a checkpoint can be taken
  /\ <>(\E n \in Node : CanTakeCheckpoint[n])
  \* If a node can take a checkpoint, eventually it will take a checkpoint
  /\ \A n \in Node :
    /\ CanTakeCheckpoint[n] ~>
      \/ IsTakingCheckpoint[n]
      \/ ~IsNodeUp[n]
      \/ CurrentLease[n].counter < TimeoutCounter
  \* If a node takes a checkpoint, eventually it will complete or timeout
  /\ \A n \in Node :
    /\ IsTakingCheckpoint[n] ~>
      \/ LastVotePayload[n] = ExecutionCounter[n]
      \/ ~IsNodeUp[n]
      \/ CurrentLease[n].counter < TimeoutCounter
  \* Eventually, a checkpoint will be completed
  /\ <>(LatestCheckpoint /= BlankLog)

(***************************************************************************)
(* Whether the dst node will receive a message from the src node.          *)
(***************************************************************************)
ConnectedOneWay(src, dst) ==
  /\ IsNodeUp[src]
  /\ IsNodeUp[dst]
  /\ NetworkPath[src, dst]

(***************************************************************************)
(* Whether the two nodes can talk to one another.                          *)
(***************************************************************************)
Connected(src, dst) ==
  /\ ConnectedOneWay(src, dst)
  /\ ConnectedOneWay(dst, src)

(***************************************************************************)
(* Whether we have quorum from the given prospective leader node.          *)
(***************************************************************************)
HaveQuorumFrom[leader \in Node] ==
  LET available == {n \in Node : Connected(leader, n)} IN
  /\ IsNodeUp[leader]
  /\ Cardinality(available) >= Majority

(***************************************************************************)
(* Whether we have a leader and that leader has quorum.                    *)
(***************************************************************************)
HaveQuorum ==
  /\ Leader /= NoNode
  /\ HaveQuorumFrom[Leader]

(***************************************************************************)
(* A node fails, losing all volatile local state.                          *)
(***************************************************************************)
NodeFailure(n) ==
  /\ IsNodeUp' = [IsNodeUp EXCEPT ![n] = FALSE]
  /\ Leader' = IF n = Leader THEN NoNode ELSE Leader
  /\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = MinLogIndex]
  /\ LastVotePayload' = [LastVotePayload EXCEPT ![n] = MinLogIndex]
  /\ CurrentLease' = [CurrentLease EXCEPT ![n] = NoCheckpointLease]
  /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
  /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<NetworkPath>>
  /\ UNCHANGED <<ReplicatedLog>>
  /\ UNCHANGED <<TimeoutCounter, LatestCheckpoint>>

(***************************************************************************)
(* A node recovers. State is first rehydrated from the last checkpoint,    *)
(* with the node's locally-persisted log filling in any gaps after that.   *)
(***************************************************************************)
NodeRecovery(n) ==
  /\ ~IsNodeUp[n]
  /\ IsNodeUp' = [IsNodeUp EXCEPT ![n] = TRUE]
  /\ ReplicatedLog' =
    [ReplicatedLog EXCEPT ![n] =
      SubSeq(LatestCheckpoint.log, MinLogIndex, LatestCheckpoint.counter - 1)
        \o SubSeq(@, LatestCheckpoint.counter, Len(@))]
  /\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = LatestCheckpoint.counter]
  /\ LastVotePayload' = [LastVotePayload EXCEPT ![n] = MinLogIndex]
  /\ CurrentLease' = [CurrentLease EXCEPT ![n] = NoCheckpointLease]
  /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
  /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<NetworkPath>>
  /\ UNCHANGED <<Leader>>
  /\ UNCHANGED <<TimeoutCounter, LatestCheckpoint>>

(***************************************************************************)
(* A network link between two nodes fails in one direction.                *)
(***************************************************************************)
NetworkFailure(src, dst) ==
  /\ src /= dst
  /\ NetworkPath' = [NetworkPath EXCEPT ![src, dst] = FALSE]
  /\ UNCHANGED <<IsNodeUp>>
  /\ UNCHANGED PaxosVars
  /\ UNCHANGED CheckpointVars

(***************************************************************************)
(* A network link between two nodes recovers.                              *)
(***************************************************************************)
NetworkRecovery(src, dst) ==
  /\ NetworkPath' = [NetworkPath EXCEPT ![src, dst] = TRUE]
  /\ UNCHANGED <<IsNodeUp>>
  /\ UNCHANGED PaxosVars
  /\ UNCHANGED CheckpointVars

(***************************************************************************)
(* Elects a new leader if one is not currently elected.                    *)
(* We can safely assume nodes currently taking a backup are excluded from  *)
(* the leader election process, because their state is too far behind.     *)
(* The leader is required to be completely caught up, and thus cannot have *)
(* any unprocessed replicated requests.                                    *)
(***************************************************************************)
ElectLeader(n) ==
  /\ Leader = NoNode
  /\ IsNodeUp[n]
  /\ ~IsTakingCheckpoint[n]
  /\ HaveQuorumFrom[n]
  /\ ExecutionCounter[n] = FirstOpenIndex
  /\ Leader' = n
  /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
  /\ UNCHANGED EnvironmentVars
  /\ UNCHANGED <<ReplicatedLog, ExecutionCounter, LastVotePayload>>
  /\ UNCHANGED <<CurrentLease, IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>


(***************************************************************************)
(* Critical logic determining whether we should replace the current lease. *)
(***************************************************************************)
ShouldReplaceLease(currentLease) ==
  \* Current lease has timed out
  \/ currentLease.counter < TimeoutCounter
  \* Snapshot has been completed & reported to leader by node
  \/  /\ Connected(Leader, currentLease.node)
      /\ currentLease.counter < LastVotePayload[currentLease.node]

(***************************************************************************)
(* The leader designates an arbitrary node to take a checkpoint. This is   *)
(* done by sending a replicated request to all nodes in the quorum. The    *)
(* request contains the node selected to perform a checkpoint.             *)
(***************************************************************************)
SendReplicatedRequest(prospect) ==
  LET currentLease == CurrentLease[Leader] IN
  LET index == FirstOpenIndex IN
  /\ HaveQuorum
  /\ Leader /= prospect
  /\ Connected(Leader, prospect)
  /\ currentLease /= NoCheckpointLease => ShouldReplaceLease(currentLease)
  /\ ReplicatedLog' =
    [n \in Node |->
      IF ConnectedOneWay(Leader, n)
      THEN WriteLog(n, index, prospect)
      ELSE ReplicatedLog[n]]
  /\ CurrentLease' = [
      CurrentLease EXCEPT ![Leader] = [
        node    |-> prospect,
        counter |-> index
      ]
    ]
  /\ UNCHANGED EnvironmentVars
  /\ UNCHANGED <<Leader, ExecutionCounter, LastVotePayload>>
  /\ UNCHANGED <<CanTakeCheckpoint, IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

(***************************************************************************)
(* Propagates chosen values to a node which might have missed them.        *)
(***************************************************************************)
PropagateReplicatedRequest(src, dst) ==
  /\ ConnectedOneWay(src, dst)
  /\ ReplicatedLog' = [ReplicatedLog EXCEPT ![dst] = MergeLogs(src, dst)]
  /\ UNCHANGED EnvironmentVars
  /\ UNCHANGED <<Leader, ExecutionCounter, LastVotePayload>>
  /\ UNCHANGED CheckpointVars

(***************************************************************************)
(* The node processes a replicated request. If the request specifies the   *)
(* node processing the request, and the node is not currently leader, then *)
(* the node marks itself as able to take a checkpoint.                     *)
(***************************************************************************)
ProcessReplicatedRequest(n) ==
  LET request == ReadLog(n, ExecutionCounter[n]) IN
  LET isTimedOut == ExecutionCounter[n] < TimeoutCounter IN
  /\ IsNodeUp[n]
  /\ ~IsTakingCheckpoint[n]
  /\ request /= NoNode
  /\ CanTakeCheckpoint' = [
      CanTakeCheckpoint EXCEPT ![n] =
        /\ Leader /= n
        /\ n = request
        /\ ~isTimedOut
    ]
  /\ CurrentLease' =
      IF n = Leader
      THEN CurrentLease
      ELSE [
        CurrentLease EXCEPT ![n] =
          IF isTimedOut
          THEN NoCheckpointLease
          ELSE [node |-> request, counter |-> ExecutionCounter[n]]
      ]
  /\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = @ + 1]
  /\ UNCHANGED EnvironmentVars
  /\ UNCHANGED <<Leader, ReplicatedLog, LastVotePayload>>
  /\ UNCHANGED <<IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

(***************************************************************************)
(* A node begins a checkpoint if it believes it is able.                   *)
(***************************************************************************)
StartCheckpoint(n) ==
  /\ CanTakeCheckpoint[n]
  /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = TRUE]
  /\ UNCHANGED EnvironmentVars
  /\ UNCHANGED PaxosVars
  /\ UNCHANGED <<CurrentLease, CanTakeCheckpoint, TimeoutCounter, LatestCheckpoint>>

(***************************************************************************)
(* Completes a checkpoint successfully.                                    *)
(***************************************************************************)
FinishCheckpoint(n) ==
  /\ IsTakingCheckpoint[n]
  /\ LastVotePayload' = [LastVotePayload EXCEPT ![n] = ExecutionCounter[n]]
  /\ CurrentLease' = [CurrentLease EXCEPT ![n] = NoCheckpointLease]
  /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
  /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
  /\ LatestCheckpoint' = [
      log     |-> SubSeq(
                    ReplicatedLog[n],
                    MinLogIndex,
                    ExecutionCounter[n] - 1
                  ),
      counter |-> ExecutionCounter[n]
    ]
  /\ UNCHANGED EnvironmentVars
  /\ UNCHANGED <<Leader, ReplicatedLog, ExecutionCounter>>
  /\ UNCHANGED <<TimeoutCounter>>

(***************************************************************************)
(* Increments the timeout counter; while in a real-world system we can't   *)
(* expect every node to have its local time flow at the same rate, the     *)
(* specific system being modeled will drop a node from the replica set if  *)
(* its time dilation is beyond a small margin relative to the primary.     *)
(***************************************************************************)
TriggerTimeout ==
  /\ \E n \in Node : ReadLog(n, TimeoutCounter) /= NoNode
  /\ TimeoutCounter' = TimeoutCounter + 1
  /\ CanTakeCheckpoint' = [
      n \in Node |->
        /\ CanTakeCheckpoint[n]
        /\ CurrentLease[n].counter > TimeoutCounter
    ]
  /\ IsTakingCheckpoint' = [
      n \in Node |->
        /\ IsTakingCheckpoint[n]
        /\ CurrentLease[n].counter > TimeoutCounter
    ]
  /\ UNCHANGED EnvironmentVars
  /\ UNCHANGED PaxosVars
  /\ UNCHANGED <<CurrentLease, LatestCheckpoint>>

(***************************************************************************)
(* The initial system state. All nodes healthy, log is blank.              *)
(***************************************************************************)
Init ==
  /\ IsNodeUp = [n \in Node |-> TRUE]
  /\ NetworkPath = [src, dst \in Node |-> TRUE]
  /\ Leader = NoNode
  /\ ReplicatedLog = [n \in Node |-> BlankLog]
  /\ ExecutionCounter = [n \in Node |-> MinLogIndex]
  /\ LastVotePayload = [n \in Node |-> MinLogIndex]
  /\ CurrentLease = [n \in Node |-> NoCheckpointLease]
  /\ CanTakeCheckpoint = [n \in Node |-> FALSE]
  /\ IsTakingCheckpoint = [n \in Node |-> FALSE]
  /\ TimeoutCounter = MinLogIndex
  /\ LatestCheckpoint = [log |-> BlankLog, counter |-> MinLogIndex]

(***************************************************************************)
(* The next-state relation.                                                *)
(***************************************************************************)
Next ==
  \/ \E n \in Node : NodeFailure(n)
  \/ \E n \in Node : NodeRecovery(n)
  \/ \E src, dst \in Node : NetworkFailure(src, dst)
  \/ \E src, dst \in Node : NetworkRecovery(src, dst)
  \/ \E n \in Node : ElectLeader(n)
  \/ \E n \in Node : SendReplicatedRequest(n)
  \/ \E src, dst \in Node : PropagateReplicatedRequest(src, dst)
  \/ \E n \in Node : ProcessReplicatedRequest(n)
  \/ \E n \in Node : StartCheckpoint(n)
  \/ \E n \in Node : FinishCheckpoint(n)
  \/ TriggerTimeout

(***************************************************************************)
(* Assumptions that good things eventually happen.                         *)
(***************************************************************************)
TemporalAssumptions ==
  /\ \A n \in Node : WF_AllVars(NodeRecovery(n))
  /\ \A src, dst \in Node : WF_AllVars(NetworkRecovery(src, dst))
  /\ \A n \in Node : SF_AllVars(ElectLeader(n))
  /\ \A n \in Node : SF_AllVars(SendReplicatedRequest(n))
  /\ \A src, dst \in Node : SF_AllVars(PropagateReplicatedRequest(src, dst))
  /\ \A n \in Node : SF_AllVars(ProcessReplicatedRequest(n))
  /\ \A n \in Node : SF_AllVars(StartCheckpoint(n))
  /\ \A n \in Node : SF_AllVars(FinishCheckpoint(n))

(***************************************************************************)
(* The spec, defining the set of all system behaviours.                    *)
(***************************************************************************)
Spec ==
  /\ Init
  /\ [][Next]_AllVars
  /\ TemporalAssumptions

(***************************************************************************)
(* Want to show: the set of all behaviours satisfies our requirements.     *)
(***************************************************************************)
THEOREM Spec =>
  /\ []TypeInvariant
  /\ []SafetyInvariant
  /\ []TemporalInvariant

=============================================================================

