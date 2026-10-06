---- MODULE MultiPaxos_MC ----
EXTENDS MultiPaxos

(******************************)
(* Symmetry sets declaration. *)
(******************************)

ConditionalPerm(set) == IF Cardinality(set) > 1
                          THEN Permutations(set)
                          ELSE {}

SymmetricPerms ==      ConditionalPerm(Replicas)
                  \cup ConditionalPerm(Writes)
                  \cup ConditionalPerm(Reads)

----------

(***********************************)
(* TLC model checking config defs. *)
(***********************************)
MCTGuard == 1
MCTLease == 1

MCBallots == 1..2

MCTimes == 1..3
MCTimesShort == 1..2

runFinished == \/ terminated
               \/ \A r \in Replicas:
                    \/ crashed[r]
                    \/ time[r] + 1 \notin Times
                    \* stop exploration when all commands processed, or when all
                    \* replicas either crashed or reached max time ticks

MCNext == /\ ~runFinished
          /\ Next

MCSpec == Init /\ [][MCNext]_vars

----------

(*******************************)
(* Linearizability constraint. *)
(*******************************)
IsLinearOrder(order) ==
    /\ {order[j]: j \in 1..Len(order)} = Commands
    /\ \A j \in 1..Len(order):
            \E k \in 0..(j-1):
                /\ (k = 0 \/ order[k] \in Writes)
                /\ \A l \in (k+1)..(j-1): order[l] \in Reads
                /\ AckEvent(order[j], IF k = 0 THEN "nil" ELSE order[k])
                       \in Range(observed)
        \* every command in the linear order observed the last write before it

ObeysRealTime(order) ==
    \A i, j \in 1..Len(observed):
        (/\ observed[i].type = "Ack"
         /\ observed[j].type = "Req"
         /\ i < j)
            => \E k, l \in 1..Len(order):
                   /\ order[k] = observed[i].cmd
                   /\ order[l] = observed[j].cmd
                   /\ k < l
        \* if command j started after command i was acknowledged, j is ordered
        \* after i

Linearizability ==
    terminated =>
        \E order \in [1..NumCommands -> Commands]:
            /\ IsLinearOrder(order)
            /\ ObeysRealTime(order)

THEOREM Spec => Linearizability

====
