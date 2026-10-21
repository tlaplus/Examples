---------------------------- MODULE DiningPhilosophers ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N \* Number of philosophers
ASSUME NIsPosNat == N \in Nat \ {0}

P == 1..N

LeftFork(p) == p
RightFork(p) == (p % N) + 1

ASSUME ForksDistinct == \A p \in P : RightFork(p) \in P /\ RightFork(p) # LeftFork(p)
ASSUME ForksCovered == {RightFork(p) : p \in P} = P

Neighbors(p) ==
    {q \in P \ {p} : {LeftFork(q), RightFork(q)} \cap {LeftFork(p), RightFork(p)} # {}}

VARIABLES philosophers, forks, waits
vars == <<philosophers, forks, waits>>

TypeOK ==
    /\ philosophers \in [P -> SUBSET P]
    /\ forks \in SUBSET P
    /\ waits \in [P -> SUBSET P]

Init ==
    \* each philosopher starts with no forks
    /\ philosophers = [ p \in P |-> {} ]
    \* all forks are available
    /\ forks = 1..N
    \* no philosopher has eaten yet
    /\ waits = [ p \in P |-> {} ]

TakeBoth(p) ==
    \* p has let its neighbors eat since it last ate.
    /\ waits[p] = {}
    /\ {LeftFork(p), RightFork(p)} \subseteq forks
    /\ forks' = forks \ {LeftFork(p), RightFork(p)}
    /\ philosophers' = [philosophers EXCEPT ![p] = {LeftFork(p), RightFork(p)}]
    /\ waits' = [q \in P |-> waits[q] \ {p}]

Release(p) ==
    /\ philosophers[p] = {LeftFork(p), RightFork(p)}
    /\ forks' = forks \cup {LeftFork(p), RightFork(p)}
    /\ philosophers' = [philosophers EXCEPT ![p] = {}]
    \* p waits until both neighbors have eaten.
    /\ waits' = [waits EXCEPT ![p] = Neighbors(p)]

Next ==
    \E p \in P:
        \/ TakeBoth(p)
        \/ Release(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in P :
        SF_vars(TakeBoth(p) \/ Release(p))

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
        waits |-> waits,
        eating |-> [ p \in DOMAIN philosophers |-> ThinkHungryEat(p) ]
    ]

-----------------------------------------------------------------------------


=====
