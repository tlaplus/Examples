---------------------------- MODULE DiningPhilosophers ----------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N \* Number of philosophers
ASSUME NIsPosNat == N \in Nat \ {0}

P == 1..N

LeftFork(p) == p
RightFork(p) == (p % N) + 1

ASSUME ForksDistinct == \A p \in P : RightFork(p) \in P /\ RightFork(p) # LeftFork(p)
ASSUME ForksCovered == {RightFork(p) : p \in P} = P

Neighbors(p) ==
    {q \in P \ {p} : {LeftFork(q), RightFork(q)} \cap {LeftFork(p), RightFork(p)} # {}}

VARIABLES philosophers, forks, queue
vars == <<philosophers, forks, queue>>

TypeOK ==
    /\ philosophers \in [P -> SUBSET P]
    /\ forks \in SUBSET P
    /\ queue \in Seq(P)

Init ==
    \* each philosopher starts with no forks
    /\ philosophers = [ p \in P |-> {} ]
    \* all forks are available
    /\ forks = 1..N
    \* the waiter's queue of hungry philosophers is empty
    /\ queue = <<>>

Request(p) ==
    /\ philosophers[p] = {}
    /\ \A i \in 1..Len(queue) : queue[i] # p
    /\ queue' = Append(queue, p)
    /\ UNCHANGED <<philosophers, forks>>

TakeBoth(p) ==
    \* The waiter serves p once no neighbor of p asked before p.
    /\ \E i \in 1..Len(queue) :
        /\ queue[i] = p
        /\ \A j \in 1..(i - 1) : queue[j] \notin Neighbors(p)
        /\ queue' = SubSeq(queue, 1, i - 1) \o SubSeq(queue, i + 1, Len(queue))
    /\ {LeftFork(p), RightFork(p)} \subseteq forks
    /\ forks' = forks \ {LeftFork(p), RightFork(p)}
    /\ philosophers' = [philosophers EXCEPT ![p] = {LeftFork(p), RightFork(p)}]

Release(p) ==
    /\ philosophers[p] = {LeftFork(p), RightFork(p)}
    /\ forks' = forks \cup {LeftFork(p), RightFork(p)}
    /\ philosophers' = [philosophers EXCEPT ![p] = {}]
    /\ UNCHANGED queue

Next ==
    \E p \in P:
        \/ Request(p)
        \/ TakeBoth(p)
        \/ Release(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in P :
        SF_vars(Request(p) \/ TakeBoth(p) \/ Release(p))

IsEating(p) ==
    Cardinality(philosophers[p]) = 2

NoDeadlock ==
    ENABLED Next

NoLivelock ==
    []<>(\E p \in P: IsEating(p))

NoStarvation ==
    \A p \in P: []<>IsEating(p)

-----

Alias ==
    LET ThinkHungryEat(p) ==
        IF IsEating(p) THEN "eating"
        ELSE IF Cardinality(philosophers[p]) = 1 THEN "hungry"
        ELSE "thinking" IN
    [
        philosophers |-> philosophers,
        forks |-> forks,
        queue |-> queue,
        eating |-> [ p \in DOMAIN philosophers |-> ThinkHungryEat(p) ]
    ]

-----------------------------------------------------------------------------


=====
