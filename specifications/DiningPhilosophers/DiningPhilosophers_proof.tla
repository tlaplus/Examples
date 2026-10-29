------------------------- MODULE DiningPhilosophers_proof -------------------------
(***************************************************************************)
(* Proof that the solution in DiningPhilosophers is starvation free: every *)
(* philosopher eats infinitely often.                                      *)
(*                                                                         *)
(* Odd philosophers take their left fork first, and even philosophers      *)
(* take their right fork first.  Either way, each philosopher first takes  *)
(* the lower-ranked of its two forks, where odd forks but fork 1 rank      *)
(* lowest, then fork 1, then the even forks (a resource hierarchy).        *)
(*                                                                         *)
(* A philosopher who holds fork f either eats, and then releases f, or     *)
(* holds f as its low fork and waits for its high fork, whose rank is      *)
(* higher.  By induction from the highest rank down, every fork is free    *)
(* infinitely often, so strong fairness lets every philosopher take its    *)
(* low fork, then its high fork, and eat.                                  *)
(***************************************************************************)
EXTENDS DiningPhilosophers, TLAPS, NaturalsInduction, FiniteSetTheorems

-----------------------------------------------------------------------------
(***************************************************************************)
(* Fork numbering.                                                         *)
(***************************************************************************)

LEMMA NAtLeastTwo == N \in Nat /\ N >= 2
<1>1. N \in Nat /\ N # 0
  BY NIsPosNat
<1>2. N # 1
  <2>. SUFFICES ASSUME N = 1 PROVE FALSE
    OBVIOUS
  <2>1. 1 \in P
    BY <1>1 DEF P
  <2>2. RightFork(1) # LeftFork(1)
    BY <2>1, ForksDistinct
  <2>. QED
    BY <2>2 DEF RightFork, LeftFork
<1>. QED
  BY <1>1, <1>2

LEMMA RightForkDef ==
    \A q \in P : RightFork(q) = IF q = N THEN 1 ELSE q + 1
BY NAtLeastTwo DEF P, RightFork

\* The fork that a philosopher takes first, and the one it takes second.
LowFork(p)  == IF p % 2 = 0 THEN RightFork(p) ELSE LeftFork(p)
HighFork(p) == IF p % 2 = 0 THEN LeftFork(p) ELSE RightFork(p)

Rank(f) == IF f % 2 = 0 THEN 2 ELSE IF f = 1 THEN 1 ELSE 0

LEMMA RankType == \A f \in P : Rank(f) \in 0..2
BY DEF Rank

LEMMA ForkFacts ==
    \A q \in P :
        /\ LowFork(q) \in P
        /\ HighFork(q) \in P
        /\ LowFork(q) # HighFork(q)
        /\ Rank(LowFork(q)) < Rank(HighFork(q))
        /\ {LowFork(q), HighFork(q)} = {LeftFork(q), RightFork(q)}
BY NAtLeastTwo, RightForkDef DEF P, LowFork, HighFork, LeftFork, Rank

LEMMA Parity == \A q \in P : q % 2 = 0 \/ q % 2 = 1
BY DEF P

\* The philosopher whose right fork is f.
Pred(f) == IF f = 1 THEN N ELSE f - 1

LEMMA PredInP == \A f \in P : Pred(f) \in P
BY NAtLeastTwo DEF P, Pred

\* Fork f is only ever held by philosopher f or philosopher Pred(f).
LEMMA Holders ==
    \A f, q \in P : f \in {LowFork(q), HighFork(q)} => q = f \/ q = Pred(f)
BY NAtLeastTwo, ForkFacts, RightForkDef DEF P, LeftFork, Pred

-----------------------------------------------------------------------------
(***************************************************************************)
(* Inductive invariant.                                                    *)
(***************************************************************************)

Idle(p)   == philosophers[p] = {}
Hungry(p) == philosophers[p] = {LowFork(p)}
Eating(p) == philosophers[p] = {LowFork(p), HighFork(p)}

Phases == \A p \in P : Idle(p) \/ Hungry(p) \/ Eating(p)

\* A fork lies on the table iff no one holds it ...
OnTable == \A f \in P : f \in forks <=> \A p \in P : f \notin philosophers[p]

\* ... and no two philosophers hold the same fork.
Exclusive == \A p, q \in P : p # q => philosophers[p] \cap philosophers[q] = {}

Inv == TypeOK /\ Phases /\ OnTable /\ Exclusive

\* TakeLeft and TakeRight, seen as taking the low fork, then the high one.
TakeLow(p) ==
    /\ philosophers[p] = {}
    /\ LowFork(p) \in forks
    /\ forks' = forks \ {LowFork(p)}
    /\ philosophers' = [philosophers EXCEPT ![p] = {LowFork(p)}]

TakeHigh(p) ==
    /\ philosophers[p] = {LowFork(p)}
    /\ HighFork(p) \in forks
    /\ forks' = forks \ {HighFork(p)}
    /\ philosophers' = [philosophers EXCEPT ![p] = {LowFork(p), HighFork(p)}]

NextLH == \E p \in P : TakeLow(p) \/ TakeHigh(p) \/ Release(p)

LEMMA TakeAgree ==
    ASSUME Inv, NEW p \in P, TakeLeft(p) \/ TakeRight(p)
    PROVE  TakeLow(p) \/ TakeHigh(p)
<1>. USE DEF Inv, TypeOK, LowFork, HighFork
<1>1. CASE TakeLeft(p) /\ p % 2 = 1
  <2>1. LeftFork(p) \in P /\ LeftFork(p) \notin philosophers[p]
    BY <1>1 DEF TakeLeft, OnTable, LeftFork
  <2>2. philosophers[p] = {}
    BY <2>1, <1>1 DEF Phases, Idle, Hungry, Eating
  <2>. QED
    BY <1>1, <2>2, Zenon DEF TakeLeft, TakeLow
<1>2. CASE TakeLeft(p) /\ p % 2 = 0
  BY <1>2, Zenon DEF TakeLeft, TakeHigh
<1>3. CASE TakeRight(p) /\ p % 2 = 1
  BY <1>3, Isa DEF TakeRight, TakeHigh
<1>4. CASE TakeRight(p) /\ p % 2 = 0
  <2>1. RightFork(p) \in P /\ RightFork(p) \notin philosophers[p]
    BY <1>4, ForksDistinct DEF TakeRight, OnTable
  <2>2. philosophers[p] = {}
    BY <2>1, <1>4 DEF Phases, Idle, Hungry, Eating
  <2>. QED
    BY <1>4, <2>2, Zenon DEF TakeRight, TakeLow
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, Parity

LEMMA NextAgree == ASSUME Inv, Next PROVE NextLH
BY TakeAgree DEF Next, NextLH

\* What each action does, stated pointwise.
LEMMA TakeLowFrame ==
    ASSUME TypeOK, NEW p \in P, TakeLow(p)
    PROVE  /\ philosophers[p] = {} /\ LowFork(p) \in forks
           /\ forks' = forks \ {LowFork(p)}
           /\ philosophers'[p] = {LowFork(p)}
           /\ \A r \in P : r # p => philosophers'[r] = philosophers[r]
BY DEF TypeOK, TakeLow

LEMMA TakeHighFrame ==
    ASSUME TypeOK, NEW p \in P, TakeHigh(p)
    PROVE  /\ philosophers[p] = {LowFork(p)} /\ HighFork(p) \in forks
           /\ forks' = forks \ {HighFork(p)}
           /\ philosophers'[p] = {LowFork(p), HighFork(p)}
           /\ \A r \in P : r # p => philosophers'[r] = philosophers[r]
BY DEF TypeOK, TakeHigh

LEMMA ReleaseFrame ==
    ASSUME TypeOK, NEW p \in P, Release(p)
    PROVE  /\ philosophers[p] = {LowFork(p), HighFork(p)}
           /\ forks' = forks \cup {LowFork(p), HighFork(p)}
           /\ philosophers'[p] = {}
           /\ \A r \in P : r # p => philosophers'[r] = philosophers[r]
BY ForkFacts DEF TypeOK, Release

THEOREM TypeOKInit == Init => TypeOK
BY DEF Init, TypeOK, P

THEOREM TypeOKNext == TypeOK /\ [Next]_vars => TypeOK'
<1>. SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  OBVIOUS
<1>. USE ForkFacts DEF TypeOK
<1>1. ASSUME NEW p \in P, TakeLeft(p) PROVE TypeOK'
  BY <1>1 DEF TakeLeft, LeftFork
<1>2. ASSUME NEW p \in P, TakeRight(p) PROVE TypeOK'
  BY <1>2, ForksDistinct DEF TakeRight
<1>3. ASSUME NEW p \in P, Release(p) PROVE TypeOK'
  BY <1>3, ReleaseFrame DEF Release
<1>4. CASE UNCHANGED vars
  BY <1>4 DEF vars
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

THEOREM PhasesNext == Inv /\ [Next]_vars => Phases'
<1>. SUFFICES ASSUME Inv, [Next]_vars PROVE Phases'
  OBVIOUS
<1>. USE DEF Inv, Phases, Idle, Hungry, Eating
<1>1. ASSUME NEW p \in P, TakeLow(p) PROVE Phases'
  BY <1>1, TakeLowFrame
<1>2. ASSUME NEW p \in P, TakeHigh(p) PROVE Phases'
  BY <1>2, TakeHighFrame
<1>3. ASSUME NEW p \in P, Release(p) PROVE Phases'
  BY <1>3, ReleaseFrame
<1>4. CASE UNCHANGED vars
  BY <1>4 DEF vars
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, NextAgree DEF NextLH

THEOREM OnTableNext == Inv /\ [Next]_vars => OnTable'
<1>. SUFFICES ASSUME Inv, [Next]_vars, NEW g \in P
              PROVE  g \in forks' <=> \A r \in P : g \notin philosophers'[r]
  BY DEF OnTable
<1>. USE ForkFacts DEF Inv, TypeOK, OnTable
<1>1. ASSUME NEW p \in P, TakeLow(p)
      PROVE  g \in forks' <=> \A r \in P : g \notin philosophers'[r]
  <2>1. CASE g = LowFork(p)
    BY <1>1, <2>1, TakeLowFrame
  <2>2. CASE g # LowFork(p)
    <3>1. \A r \in P : g \in philosophers'[r] <=> g \in philosophers[r]
      BY <1>1, <2>2, TakeLowFrame
    <3>. QED
      BY <1>1, <2>2, <3>1, TakeLowFrame
  <2>. QED
    BY <2>1, <2>2
<1>2. ASSUME NEW p \in P, TakeHigh(p)
      PROVE  g \in forks' <=> \A r \in P : g \notin philosophers'[r]
  <2>1. CASE g = HighFork(p)
    BY <1>2, <2>1, TakeHighFrame
  <2>2. CASE g # HighFork(p)
    <3>1. \A r \in P : g \in philosophers'[r] <=> g \in philosophers[r]
      BY <1>2, <2>2, TakeHighFrame
    <3>. QED
      BY <1>2, <2>2, <3>1, TakeHighFrame
  <2>. QED
    BY <2>1, <2>2
<1>3. ASSUME NEW p \in P, Release(p)
      PROVE  g \in forks' <=> \A r \in P : g \notin philosophers'[r]
  <2>1. CASE g \in {LowFork(p), HighFork(p)}
    BY <1>3, <2>1, ReleaseFrame, Zenon DEF Exclusive
  <2>2. CASE g \notin {LowFork(p), HighFork(p)}
    <3>1. \A r \in P : g \in philosophers'[r] <=> g \in philosophers[r]
      BY <1>3, <2>2, ReleaseFrame
    <3>. QED
      BY <1>3, <2>2, <3>1, ReleaseFrame
  <2>. QED
    BY <2>1, <2>2
<1>4. CASE UNCHANGED vars
  BY <1>4 DEF vars
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, NextAgree DEF NextLH

THEOREM ExclusiveNext == Inv /\ [Next]_vars => Exclusive'
<1>. SUFFICES ASSUME Inv, [Next]_vars,
                     NEW r1 \in P, NEW r2 \in P, r1 # r2
              PROVE  philosophers'[r1] \cap philosophers'[r2] = {}
  BY DEF Exclusive
<1>. USE DEF Inv, TypeOK
<1>1. ASSUME NEW p \in P, TakeLow(p)
      PROVE  philosophers'[r1] \cap philosophers'[r2] = {}
  <2>1. \A r \in P : LowFork(p) \notin philosophers[r]
    BY <1>1, TakeLowFrame DEF OnTable
  <2>. QED
    BY <1>1, <2>1, TakeLowFrame DEF Exclusive
<1>2. ASSUME NEW p \in P, TakeHigh(p)
      PROVE  philosophers'[r1] \cap philosophers'[r2] = {}
  <2>1. \A r \in P : HighFork(p) \notin philosophers[r]
    BY <1>2, TakeHighFrame DEF OnTable
  <2>2. \A r \in P : r # p => LowFork(p) \notin philosophers[r]
    <3>. SUFFICES ASSUME NEW r \in P, r # p PROVE LowFork(p) \notin philosophers[r]
      OBVIOUS
    <3>1. philosophers[p] \cap philosophers[r] = {}
      BY DEF Exclusive
    <3>. QED
      BY <1>2, <3>1, TakeHighFrame
  <2>. QED
    BY <1>2, <2>1, <2>2, TakeHighFrame DEF Exclusive
<1>3. ASSUME NEW p \in P, Release(p)
      PROVE  philosophers'[r1] \cap philosophers'[r2] = {}
  BY <1>3, ReleaseFrame DEF Exclusive
<1>4. CASE UNCHANGED vars
  BY <1>4 DEF vars, Exclusive
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, NextAgree DEF NextLH

THEOREM InvInit == Init => Inv
BY ForkFacts, TypeOKInit DEF Init, Inv, Phases, OnTable, Exclusive, Idle, P

THEOREM InvNext == Inv /\ [Next]_vars => Inv'
BY TypeOKNext, PhasesNext, OnTableNext, ExclusiveNext DEF Inv

THEOREM InvSpec == Spec => []Inv
BY InvInit, InvNext, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* The steps of a single philosopher.                                      *)
(***************************************************************************)

Act(p) == TakeLeft(p) \/ TakeRight(p) \/ Release(p)

LEMMA SpecNext == Spec => [][Next]_vars
BY Isa DEF Spec

LEMMA SpecFair == \A q \in P : Spec => SF_vars(Act(q))
BY Isa DEF Spec, Act

\* A step either is a step of q or leaves q's forks alone.
LEMMA NextSplit ==
    ASSUME Inv, [Next]_vars, NEW q \in P
    PROVE  <<Act(q)>>_vars \/ philosophers'[q] = philosophers[q]
<1>1. CASE UNCHANGED vars
  BY <1>1 DEF vars
<1>2. ASSUME NEW p \in P, p # q, Act(p)
      PROVE  philosophers'[q] = philosophers[q]
  BY <1>2 DEF Act, TakeLeft, TakeRight, Release, Inv, TypeOK
<1>3. CASE Act(q)
  BY <1>3 DEF vars
<1>. QED
  BY <1>1, <1>2, <1>3 DEF Next, Act

\* A step of q is a step of TakeLow, TakeHigh, or Release.
LEMMA ActAgree ==
    ASSUME Inv, NEW q \in P, Act(q)
    PROVE  TakeLow(q) \/ TakeHigh(q) \/ Release(q)
BY TakeAgree DEF Act

LEMMA IdleStep ==
    ASSUME Inv, NEW q \in P, Idle(q), <<Act(q)>>_vars
    PROVE  Hungry(q)'
BY ActAgree, ForkFacts DEF Inv, TypeOK, Idle, Hungry, TakeLow, TakeHigh, Release

LEMMA HungryStep ==
    ASSUME Inv, NEW q \in P, Hungry(q), <<Act(q)>>_vars
    PROVE  Eating(q)'
BY ActAgree, ForkFacts DEF Inv, TypeOK, Hungry, Eating, TakeLow, TakeHigh, Release

LEMMA EatingStep ==
    ASSUME Inv, NEW q \in P, Eating(q), <<Act(q)>>_vars
    PROVE  \A f \in philosophers[q] : f \in forks'
BY ActAgree, ForkFacts DEF Inv, TypeOK, Eating, TakeLow, TakeHigh, Release

LEMMA IdleEnabled ==
    ASSUME NEW q \in P
    PROVE  Inv /\ Idle(q) /\ LowFork(q) \in forks => ENABLED <<Act(q)>>_vars
<1>. SUFFICES ASSUME Inv, Idle(q), LowFork(q) \in forks
              PROVE  ENABLED <<Act(q)>>_vars
  OBVIOUS
<1>1. philosophers \in [P -> SUBSET P] /\ philosophers[q] = {}
  BY DEF Inv, TypeOK, Idle
<1>2. CASE q % 2 = 1
  <2>1. LeftFork(q) \in forks
    BY <1>2 DEF LowFork
  <2>2. <<[philosophers EXCEPT ![q] = philosophers[q] \cup {LeftFork(q)}],
          forks \ {LeftFork(q)}>> # <<philosophers, forks>>
    BY <1>1
  <2>3. ENABLED <<TakeLeft(q)>>_vars
    BY <1>1, <1>2, <2>1, <2>2, ExpandENABLED, Isa DEF TakeLeft, vars
  <2>. QED
    BY <2>3, ExpandENABLED, Zenon DEF Act, TakeLeft, TakeRight, Release, vars
<1>3. CASE q % 2 = 0
  <2>1. RightFork(q) \in forks
    BY <1>3 DEF LowFork
  <2>2. <<[philosophers EXCEPT ![q] = philosophers[q] \cup {RightFork(q)}],
          forks \ {RightFork(q)}>> # <<philosophers, forks>>
    BY <1>1
  <2>3. ENABLED <<TakeRight(q)>>_vars
    BY <1>1, <1>3, <2>1, <2>2, ExpandENABLED, Isa DEF TakeRight, vars
  <2>. QED
    BY <2>3, ExpandENABLED, Zenon DEF Act, TakeLeft, TakeRight, Release, vars
<1>. QED
  BY <1>2, <1>3, Parity

LEMMA HungryEnabled ==
    ASSUME NEW q \in P
    PROVE  Inv /\ Hungry(q) /\ HighFork(q) \in forks => ENABLED <<Act(q)>>_vars
<1>. SUFFICES ASSUME Inv, Hungry(q), HighFork(q) \in forks
              PROVE  ENABLED <<Act(q)>>_vars
  OBVIOUS
<1>1. philosophers \in [P -> SUBSET P] /\ philosophers[q] = {LowFork(q)}
  BY DEF Inv, TypeOK, Hungry
<1>2. LeftFork(q) # RightFork(q)
  BY ForksDistinct
<1>3. CASE q % 2 = 1
  <2>1. philosophers[q] = {LeftFork(q)} /\ RightFork(q) \in forks
    BY <1>1, <1>3 DEF LowFork, HighFork
  <2>2. <<[philosophers EXCEPT ![q] = philosophers[q] \cup {RightFork(q)}],
          forks \ {RightFork(q)}>> # <<philosophers, forks>>
    BY <1>1, <1>2, <2>1
  <2>3. (q % 2 = 1 => philosophers[q] = {LeftFork(q)}) /\ RightFork(q) \in forks
    BY <2>1
  <2>4. ENABLED <<TakeRight(q)>>_vars
    BY <2>2, <2>3, ExpandENABLED, Isa DEF TakeRight, vars
  <2>. QED
    BY <2>4, ExpandENABLED, Zenon DEF Act, TakeLeft, TakeRight, Release, vars
<1>4. CASE q % 2 = 0
  <2>1. philosophers[q] = {RightFork(q)} /\ LeftFork(q) \in forks
    BY <1>1, <1>4 DEF LowFork, HighFork
  <2>2. <<[philosophers EXCEPT ![q] = philosophers[q] \cup {LeftFork(q)}],
          forks \ {LeftFork(q)}>> # <<philosophers, forks>>
    BY <1>1, <1>2, <2>1
  <2>3. (q % 2 = 0 => philosophers[q] = {RightFork(q)}) /\ LeftFork(q) \in forks
    BY <2>1
  <2>4. ENABLED <<TakeLeft(q)>>_vars
    BY <2>2, <2>3, ExpandENABLED, Isa DEF TakeLeft, vars
  <2>. QED
    BY <2>4, ExpandENABLED, Zenon DEF Act, TakeLeft, TakeRight, Release, vars
<1>. QED
  BY <1>3, <1>4, Parity

LEMMA EatingEnabled ==
    ASSUME NEW q \in P
    PROVE  Inv /\ Eating(q) => ENABLED <<Act(q)>>_vars
<1>. SUFFICES ASSUME Inv, Eating(q)
              PROVE  ENABLED <<Act(q)>>_vars
  OBVIOUS
<1>1. philosophers \in [P -> SUBSET P]
      /\ philosophers[q] = {LeftFork(q), RightFork(q)}
  BY ForkFacts DEF Inv, TypeOK, Eating
<1>2. {LeftFork(q), RightFork(q)} # {}
  OBVIOUS
<1>3. <<[philosophers EXCEPT ![q] = {}], forks \cup {LeftFork(q), RightFork(q)}>>
        # <<philosophers, forks>>
  BY <1>1, <1>2
<1>4. ENABLED <<Release(q)>>_vars
  BY <1>1, <1>3, ExpandENABLED, Isa DEF Release, vars
<1>. QED
  BY <1>4, ExpandENABLED, Zenon DEF Act, TakeLeft, TakeRight, Release, vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Progress of a single philosopher.                                       *)
(***************************************************************************)

FreeIO(f) == []<>(f \in forks)

HeldEat(f, q) == Eating(q) /\ f \in philosophers[q]

\* Named so that the lemmas below can be instantiated: backends other than
\* PTL only see temporal formulas through opaque operators.
IdleToHungry(q)   == Idle(q) ~> Hungry(q)
HungryToEating(q) == Hungry(q) ~> Eating(q)
EatingFrees(f, q) == HeldEat(f, q) ~> (f \in forks)
HungryFrees(f, q) == (Hungry(q) /\ f = LowFork(q)) ~> (f \in forks)

LEMMA IdleHungry ==
    ASSUME NEW q \in P
    PROVE  Spec /\ FreeIO(LowFork(q)) => IdleToHungry(q)
<1>1. Inv /\ Idle(q) /\ [Next]_vars => Idle(q)' \/ Hungry(q)'
  <2>. SUFFICES ASSUME Inv, Idle(q), [Next]_vars PROVE Idle(q)' \/ Hungry(q)'
    OBVIOUS
  <2>1. CASE philosophers'[q] = philosophers[q]
    BY <2>1 DEF Idle
  <2>2. CASE <<Act(q)>>_vars
    BY <2>2, IdleStep
  <2>. QED
    BY <2>1, <2>2, NextSplit
<1>2. Inv /\ Idle(q) /\ <<Act(q)>>_vars => Hungry(q)'
  BY IdleStep
<1>3. Inv /\ Idle(q) /\ LowFork(q) \in forks => ENABLED <<Act(q)>>_vars
  BY IdleEnabled
<1>4. Spec => SF_vars(Act(q))
  BY SpecFair, Isa
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, InvSpec, SpecNext, PTL DEF FreeIO, IdleToHungry

LEMMA HungryEat ==
    ASSUME NEW q \in P
    PROVE  Spec /\ FreeIO(HighFork(q)) => HungryToEating(q)
<1>1. Inv /\ Hungry(q) /\ [Next]_vars => Hungry(q)' \/ Eating(q)'
  <2>. SUFFICES ASSUME Inv, Hungry(q), [Next]_vars PROVE Hungry(q)' \/ Eating(q)'
    OBVIOUS
  <2>1. CASE philosophers'[q] = philosophers[q]
    BY <2>1 DEF Hungry
  <2>2. CASE <<Act(q)>>_vars
    BY <2>2, HungryStep
  <2>. QED
    BY <2>1, <2>2, NextSplit
<1>2. Inv /\ Hungry(q) /\ <<Act(q)>>_vars => Eating(q)'
  BY HungryStep
<1>3. Inv /\ Hungry(q) /\ HighFork(q) \in forks => ENABLED <<Act(q)>>_vars
  BY HungryEnabled
<1>4. Spec => SF_vars(Act(q))
  BY SpecFair, Isa
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, InvSpec, SpecNext, PTL DEF FreeIO, HungryToEating

LEMMA EatRelease ==
    ASSUME NEW f \in P, NEW q \in P
    PROVE  Spec => EatingFrees(f, q)
<1>1. Inv /\ HeldEat(f, q) /\ [Next]_vars => HeldEat(f, q)' \/ (f \in forks)'
  <2>. SUFFICES ASSUME Inv, HeldEat(f, q), [Next]_vars
                PROVE  HeldEat(f, q)' \/ (f \in forks)'
    OBVIOUS
  <2>1. CASE philosophers'[q] = philosophers[q]
    BY <2>1 DEF HeldEat, Eating
  <2>2. CASE <<Act(q)>>_vars
    BY <2>2, EatingStep DEF HeldEat
  <2>. QED
    BY <2>1, <2>2, NextSplit
<1>2. Inv /\ HeldEat(f, q) /\ <<Act(q)>>_vars => (f \in forks)'
  BY EatingStep DEF HeldEat
<1>3. Inv /\ HeldEat(f, q) => ENABLED <<Act(q)>>_vars
  BY EatingEnabled DEF HeldEat
<1>4. Spec => SF_vars(Act(q))
  BY SpecFair, Isa
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, InvSpec, SpecNext, PTL DEF EatingFrees

\* A hungry philosopher who holds f as its low fork eventually frees f,
\* provided that all forks ranked above f are free infinitely often.
LEMMA HungryRelease ==
    ASSUME NEW f \in P, NEW q \in P
    PROVE  Spec /\ (\A g \in P : Rank(g) > Rank(f) => FreeIO(g)) => HungryFrees(f, q)
<1>1. CASE f = LowFork(q)
  <2>1. HighFork(q) \in P /\ Rank(HighFork(q)) > Rank(f)
    BY <1>1, ForkFacts
  <2>2. (\A g \in P : Rank(g) > Rank(f) => FreeIO(g)) => FreeIO(HighFork(q))
    BY <2>1
  <2>3. Spec /\ FreeIO(HighFork(q)) => HungryToEating(q)
    BY HungryEat
  <2>4. Spec => EatingFrees(f, q)
    BY EatRelease
  <2>5. Eating(q) => HeldEat(f, q)
    BY <1>1 DEF HeldEat, Eating
  <2>6. (Hungry(q) /\ f = LowFork(q)) => Hungry(q)
    OBVIOUS
  <2>. QED
    BY <2>2, <2>3, <2>4, <2>5, <2>6, PTL
       DEF HungryToEating, EatingFrees, HungryFrees
<1>2. CASE f # LowFork(q)
  <2>1. ~(Hungry(q) /\ f = LowFork(q))
    BY <1>2
  <2>. QED
    BY <2>1, PTL DEF HungryFrees
<1>. QED
  BY <1>1, <1>2

-----------------------------------------------------------------------------
(***************************************************************************)
(* Every fork is free infinitely often.                                    *)
(***************************************************************************)

LEMMA HeldBy ==
    ASSUME NEW f \in P
    PROVE  Inv /\ ~(f \in forks) =>
              \/ HeldEat(f, f) \/ HeldEat(f, Pred(f))
              \/ Hungry(f) /\ f = LowFork(f)
              \/ Hungry(Pred(f)) /\ f = LowFork(Pred(f))
<1>. SUFFICES ASSUME Inv, ~(f \in forks)
              PROVE  \/ HeldEat(f, f) \/ HeldEat(f, Pred(f))
                     \/ Hungry(f) /\ f = LowFork(f)
                     \/ Hungry(Pred(f)) /\ f = LowFork(Pred(f))
  OBVIOUS
<1>1. PICK q \in P : f \in philosophers[q]
  BY DEF Inv, OnTable
<1>2. f \in {LowFork(q), HighFork(q)}
  BY <1>1 DEF Inv, Phases, Idle, Hungry, Eating
<1>3. q = f \/ q = Pred(f)
  BY <1>2, Holders
<1>4. HeldEat(f, q) \/ (Hungry(q) /\ f = LowFork(q))
  BY <1>1 DEF Inv, Phases, Idle, Hungry, Eating, HeldEat
<1>. QED
  BY <1>3, <1>4

LEMMA FreeStep ==
    ASSUME NEW f \in P
    PROVE  Spec /\ (\A g \in P : Rank(g) > Rank(f) => FreeIO(g)) => FreeIO(f)
<1>1. Pred(f) \in P
  BY PredInP
<1>2. Inv /\ ~(f \in forks) =>
          \/ HeldEat(f, f) \/ HeldEat(f, Pred(f))
          \/ Hungry(f) /\ f = LowFork(f)
          \/ Hungry(Pred(f)) /\ f = LowFork(Pred(f))
  BY HeldBy
<1>3. Spec => EatingFrees(f, f)
  BY EatRelease
<1>4. Spec => EatingFrees(f, Pred(f))
  BY <1>1, EatRelease
<1>5. Spec /\ (\A g \in P : Rank(g) > Rank(f) => FreeIO(g)) => HungryFrees(f, f)
  BY HungryRelease
<1>6. Spec /\ (\A g \in P : Rank(g) > Rank(f) => FreeIO(g)) => HungryFrees(f, Pred(f))
  BY <1>1, HungryRelease
<1>. QED
  BY <1>2, <1>3, <1>4, <1>5, <1>6, InvSpec, PTL
     DEF FreeIO, EatingFrees, HungryFrees

THEOREM AllFree == \A f \in P : Spec => FreeIO(f)
<1>. DEFINE Q(m) == Spec => \A g \in P : Rank(g) + m > 2 => FreeIO(g)
<1>1. Q(0)
  BY RankType
<1>2. \A m \in Nat : Q(m) => Q(m + 1)
  <2>. SUFFICES ASSUME NEW m \in Nat, Q(m)
                PROVE  Q(m + 1)
    OBVIOUS
  <2>1. ASSUME NEW g \in P, Rank(g) + (m + 1) > 2
        PROVE  Spec => FreeIO(g)
    <3>1. CASE Rank(g) + m > 2
      BY <3>1
    <3>2. CASE ~(Rank(g) + m > 2)
      <4>1. \A h \in P : Rank(h) > Rank(g) => Rank(h) + m > 2
        BY <2>1, <3>2, RankType
      <4>2. Spec => \A h \in P : Rank(h) > Rank(g) => FreeIO(h)
        BY <4>1
      <4>. QED
        BY <4>2, FreeStep
    <3>. QED
      BY <3>1, <3>2
  <2>. QED
    BY <2>1
<1>. HIDE DEF Q
<1>3. \A m \in Nat : Q(m)
  BY <1>1, <1>2, NatInduction, Isa
<1>4. Q(3)
  BY <1>3
<1>. QED
  BY <1>4, RankType DEF Q

-----------------------------------------------------------------------------
(***************************************************************************)
(* Starvation freedom.                                                     *)
(***************************************************************************)

LEMMA EatingIsEating == \A p \in P : Eating(p) => IsEating(p)
<1>. SUFFICES ASSUME NEW p \in P, Eating(p) PROVE IsEating(p)
  OBVIOUS
<1>1. LowFork(p) # HighFork(p)
  BY ForkFacts
<1>2. IsFiniteSet({LowFork(p)}) /\ Cardinality({LowFork(p)}) = 1
  BY FS_Singleton
<1>3. Cardinality({LowFork(p)} \cup {HighFork(p)}) = 2
  BY <1>1, <1>2, FS_AddElement
<1>. QED
  BY <1>3, Zenon DEF Eating, IsEating

THEOREM StarvationFreedom
<1>. SUFFICES ASSUME NEW p \in P PROVE Spec => []<>IsEating(p)
  BY DEF NoStarvation
<1>1. Spec => FreeIO(LowFork(p))
  BY AllFree, ForkFacts
<1>2. Spec => FreeIO(HighFork(p))
  BY AllFree, ForkFacts
<1>3. Spec /\ FreeIO(LowFork(p)) => IdleToHungry(p)
  BY IdleHungry
<1>4. Spec /\ FreeIO(HighFork(p)) => HungryToEating(p)
  BY HungryEat
<1>5. Inv => Idle(p) \/ Hungry(p) \/ Eating(p)
  BY DEF Inv, Phases
<1>6. Eating(p) => IsEating(p)
  BY EatingIsEating
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, InvSpec, PTL
     DEF IdleToHungry, HungryToEating

EatsIO(p) == []<>IsEating(p)

THEOREM StarvationImpliesNoLivelock == NoStarvation => NoLivelock
<1>1. 1 \in P
  BY NIsPosNat DEF P
<1>2. NoStarvation => \A p \in P : EatsIO(p)
  BY DEF NoStarvation, EatsIO
<1>3. NoStarvation => EatsIO(1)
  BY <1>1, <1>2
<1>4. IsEating(1) => \E p \in P : IsEating(p)
  BY <1>1
<1>. QED
  BY <1>3, <1>4, PTL DEF EatsIO, NoLivelock

THEOREM LivelockFreedom
BY StarvationFreedom, StarvationImpliesNoLivelock

-----------------------------------------------------------------------------
(***************************************************************************)
(* Deadlock freedom.  If no one eats, every even fork is free, because it  *)
(* is the high fork of both philosophers who can hold it.  So a hungry     *)
(* philosopher whose high fork is even can take it.  Otherwise philosopher *)
(* 1 is idle, and fork 1 is free: philosopher N could hold it only as its  *)
(* low fork, and then N's high fork would be even.                         *)
(***************************************************************************)

LEMMA ActEnabledNext ==
    ASSUME NEW q \in P
    PROVE  (ENABLED <<Act(q)>>_vars) => ENABLED Next
BY ExpandENABLED, Zenon DEF Act, Next, TakeLeft, TakeRight, Release, vars

LEMMA EvenFree ==
    ASSUME Inv, \A q \in P : ~Eating(q), NEW f \in P, Rank(f) = 2
    PROVE  f \in forks
<1>. SUFFICES ASSUME ~(f \in forks) PROVE FALSE
  OBVIOUS
<1>1. PICK q \in P : f \in philosophers[q]
  BY DEF Inv, OnTable
<1>2. f = LowFork(q)
  BY <1>1 DEF Inv, Phases, Idle, Hungry
<1>. QED
  BY <1>2, ForkFacts, RankType

LEMMA OneForks ==
    /\ 1 \in P /\ 2 \in P /\ N \in P
    /\ LowFork(1) = 1 /\ HighFork(1) = 2 /\ Rank(2) = 2
    /\ Pred(1) = N /\ N # 1
    /\ LowFork(N) = 1 => Rank(HighFork(N)) = 2
BY NAtLeastTwo, RightForkDef DEF P, LowFork, HighFork, LeftFork, Pred, Rank

THEOREM InvNoDeadlock == Inv => NoDeadlock
<1>. SUFFICES ASSUME Inv PROVE ENABLED Next
  BY DEF NoDeadlock
<1>0. OneForks
  BY OneForks
<1>1. CASE \E q \in P : Eating(q)
  BY <1>1, EatingEnabled, ActEnabledNext
<1>2. CASE \A q \in P : ~Eating(q)
  <2>1. CASE \E q \in P : Hungry(q) /\ Rank(HighFork(q)) = 2
    <3>1. PICK q \in P : Hungry(q) /\ Rank(HighFork(q)) = 2
      BY <2>1
    <3>2. HighFork(q) \in forks
      BY <1>2, <3>1, ForkFacts, EvenFree
    <3>. QED
      BY <3>1, <3>2, HungryEnabled, ActEnabledNext
  <2>2. CASE \A q \in P : ~(Hungry(q) /\ Rank(HighFork(q)) = 2)
    <3>1. Idle(1)
      BY <1>0, <1>2, <2>2 DEF Inv, Phases
    <3>2. 1 \in forks
      <4>. SUFFICES ASSUME ~(1 \in forks) PROVE FALSE
        OBVIOUS
      <4>1. PICK r \in P : 1 \in philosophers[r]
        BY <1>0 DEF Inv, OnTable
      <4>2. Hungry(r) /\ 1 = LowFork(r)
        BY <1>2, <4>1 DEF Inv, Phases, Idle, Hungry
      <4>3. r = 1 \/ r = N
        BY <1>0, <4>2, Holders
      <4>4. r # 1
        BY <3>1, <4>1 DEF Idle
      <4>. QED
        BY <1>0, <2>2, <4>2, <4>3, <4>4
    <3>. QED
      BY <1>0, <3>1, <3>2, IdleEnabled, ActEnabledNext
  <2>. QED
    BY <2>1, <2>2
<1>. QED
  BY <1>1, <1>2

THEOREM DeadlockFreedom
BY InvNoDeadlock, InvSpec, PTL

=============================================================================
