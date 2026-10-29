---- MODULE abstract ----
EXTENDS Integers, Sequences

VARIABLES pc, counter
vars == <<pc, counter>>

\* Two threads
Threads == 1..2

\* State transition action
Trans(thread, from, to) ==
  /\ pc[thread] = from
  /\ pc' = [pc EXCEPT ![thread] = to]

\* Both threads start in the `start` state
Init ==
  /\ pc = [t \in Threads |-> "start"]
  /\ counter = 0

Next ==
  \* Pick one thread
  \/ \E t \in Threads:
     \* Move it to `done`
     /\ Trans(t, "start", "done")
     \* Increment counter
     /\ counter' = counter + 1

Spec == Init /\ [][Next]_vars

====
