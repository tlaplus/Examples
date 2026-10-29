---- MODULE bad ----
EXTENDS Integers, Sequences

VARIABLES pc, counter, tmp
vars == <<pc, counter, tmp>>

Threads == 1..2

States == {"start", "inc", "done"}

Trans(thread, from, to) ==
  /\ pc[thread] = from
  /\ pc' = [pc EXCEPT ![thread] = to]

Init ==
  /\ pc = [t \in Threads |-> "start"]
  /\ counter = 0
  /\ tmp = [t \in Threads |-> 0]

GetCounter(t) ==
  /\ tmp' = [tmp EXCEPT ![t] = counter]
  /\ UNCHANGED counter

IncCounter(t) ==
  /\ counter' = tmp[t] + 1
  /\ UNCHANGED tmp

Next ==
  \/ \E t \in Threads:
    \* Step to get the counter value
    \/ /\ Trans(t, "start", "inc")
       /\ GetCounter(t)
    \* Step to increment the counter
    \/ /\ Trans(t, "inc", "done")
       /\ IncCounter(t)

Spec == Init /\ [][Next]_vars

Mapping == 
  INSTANCE abstract WITH
    counter <- counter,
    pc <- [t \in Threads |-> 
      IF pc[t] = "inc" THEN "start"
      ELSE pc[t]
      ]

Refinement == Mapping!Spec

====
