------------------------------- MODULE CRDT_proof ---------------------------------
EXTENDS CRDT, Naturals, FiniteSets, NaturalsInduction, TLAPS

ASSUME NodeAssumption == IsFiniteSet(Node)

(***************************************************************************)
(* Proofs of safety properties.                                            *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF TypeOK, Next, Increment, Gossip, vars
<1>. QED  BY <1>1, <1>2, PTL DEF Spec, vars


THEOREM Safe == Spec => []Safety
<1>1. Init => Safety
  BY DEF Init, Safety
<1>2. TypeOK /\ Safety /\ [Next]_vars => Safety'
  BY DEF TypeOK, Safety, Next, Increment, Gossip, vars
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec, vars

THEOREM Spec => Monotonicity
<1>1. TypeOK /\ [Next]_vars => [Monotonic]_vars
  BY DEF TypeOK, Safety, Next, Increment, Gossip, vars, Monotonic
<1>. QED  BY <1>1, TypeCorrect, PTL DEF Spec, Monotonicity, vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Auxiliary definitions in preparation for the liveness proof.            *)
(* Sum the values of a vector of natural numbers indexed by Node.          *)
(* This operator could be defined using a Fold, but since there is no      *)
(* library of theorems about Fold, we define it directly from scratch.     *)
(* We then state a few facts about Sum, without proof.                     *)
(***************************************************************************)
Sum(f) ==
  LET SumS[S \in SUBSET Node] == 
          IF S = {} THEN 0
          ELSE LET x == CHOOSE x \in S : TRUE
               IN  f[x] + SumS[S \ {x}]
  IN  SumS[Node]

LEMMA SumType ==
  ASSUME NEW f \in [Node -> Nat]
  PROVE  Sum(f) \in Nat
PROOF OMITTED

LEMMA SumIsZero ==
  ASSUME NEW f \in [Node -> Nat]
  PROVE  Sum(f) = 0 <=> \A x \in Node : f[x] = 0
PROOF OMITTED

LEMMA SumWeaklyMonotonic ==
  ASSUME NEW f \in [Node -> Nat], NEW g \in [Node -> Nat],
         \A x \in Node : f[x] <= g[x]
  PROVE  Sum(f) <= Sum(g)
PROOF OMITTED

LEMMA SumStronglyMonotonic ==
  ASSUME NEW f \in [Node -> Nat], NEW g \in [Node -> Nat],
         \A x \in Node : f[x] <= g[x],
         \E x \in Node : f[x] < g[x]
  PROVE  Sum(f) < Sum(g)
PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proof of the convergence property for the specification with fairness.  *)
(***************************************************************************)

\* First prove when <<Gossip(n,o)>>_vars is enabled.

LEMMA EnabledGossip ==
  ASSUME NEW n \in Node, NEW o \in Node, TypeOK
  PROVE  (ENABLED <<Gossip(n,o)>>_vars) <=>
         \E v \in Node : counter[o][v] < counter[n][v]
<1>. USE DEF TypeOK
<1>1. ASSUME ENABLED <<Gossip(n,o)>>_vars
             PROVE   \E v \in Node : counter[o][v] < counter[n][v]
  <2>. CASE <<Gossip(n,o)>>_counter
    BY DEF Gossip
  <2>. QED  BY <1>1, ExpandENABLED DEF Gossip, vars     
<1>2. ASSUME NEW v \in Node, counter[o][v] < counter[n][v]
      PROVE  ENABLED <<Gossip(n,o)>>_vars
  <2>. DEFINE Max(a, b) == IF a > b THEN a ELSE b
              ctr == [counter EXCEPT ![o] =
                        [nv \in Node |-> Max(counter[n][nv], counter[o][nv])]]
  <2>. ctr[o][v] # counter[o][v]
    BY <1>2
  <2>. QED  BY ExpandENABLED, Zenon DEF Gossip, vars
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Definition of the termination measure.                                  *)
(* Distance(o) sums the differences between node o's knowledge of the      *)
(* counters of other nodes and their true values.                          *)
(* Measure sums Distance(o), for all nodes o.                              *)
(* We prove elementary facts about the termination measure and in          *)
(* particular show how the Gossip action interacts with it.                *)
(***************************************************************************)
DistFun(o) == [n \in Node |-> counter[n][n] - counter[o][n]]

Distance(o) == Sum(DistFun(o))

Measure == Sum([o \in Node |-> Distance(o)])

LEMMA MeasureType ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : DistFun(o) \in [Node -> Nat]
         /\ \A o \in Node : Distance(o) \in Nat
         /\ Measure \in Nat
<1>. ASSUME NEW o \in Node
     PROVE  DistFun(o) \in [Node -> Nat]
  BY DEF TypeOK, Safety, DistFun
<1>. QED  BY SumType, Zenon DEF Distance, Measure

\* We need a copy of the above theorem where all variables are primed.
\* One could derive this from MeasureType using PTL, but we just copy
\* and paste the proof.
LEMMA MeasureTypePrime ==
  ASSUME TypeOK', Safety'
  PROVE  /\ \A o \in Node : DistFun(o)' \in [Node -> Nat]
         /\ \A o \in Node : Distance(o)' \in Nat
         /\ Measure' \in Nat
<1>. ASSUME NEW o \in Node
     PROVE  DistFun(o)' \in [Node -> Nat]
  BY DEF TypeOK, Safety, DistFun
<1>. QED  BY SumType, Zenon DEF Distance, Measure

\* The termination measure is zero iff all nodes agree on the 
\* counter values of all nodes.
LEMMA MeasureIsZero ==
  ASSUME TypeOK, Safety
  PROVE  /\ \A o \in Node : Distance(o) = 0 
                 <=> \A n \in Node : counter[o][n] = counter[n][n]
         /\ Measure = 0
            <=> \A v,w,n \in Node : counter[v][n] = counter[w][n]
<1>1. ASSUME NEW o \in Node, Distance(o) = 0, NEW n \in Node
      PROVE  counter[o][n] = counter[n][n]
  BY <1>1, MeasureType, SumIsZero DEF Distance, DistFun, TypeOK, Safety
<1>2. ASSUME NEW o \in Node, \A n \in Node : counter[o][n] = counter[n][n]
      PROVE  Distance(o) = 0
  BY <1>2, MeasureType, SumIsZero DEF Distance, DistFun, TypeOK
<1>3. ASSUME Measure = 0, NEW v \in Node, NEW w \in Node, NEW n \in Node
      PROVE  counter[v][n] = counter[w][n]
  BY <1>1, <1>3, MeasureType, SumIsZero DEF Measure
<1>4. ASSUME \A v,w,n \in Node : counter[v][n] = counter[w][n]
      PROVE  Measure = 0
  BY <1>2, <1>4, MeasureType, SumIsZero DEF Measure
<1>. QED  BY <1>1, <1>2, <1>3, <1>4

\* A Gossip action will never increase the measure.
LEMMA GossipDoesntIncreaseMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         [\E n,o \in Node : Gossip(n,o)]_vars
  PROVE  /\ \A v,w \in Node : DistFun(v)'[w] <= DistFun(v)[w]
         /\ \A v \in Node : Distance(v)' <= Distance(v)
         /\ Measure' <= Measure
<1>1. CASE \E n,o \in Node : Gossip(n,o)
  <2>. ASSUME NEW v \in Node, NEW w \in Node
        PROVE  DistFun(v)'[w] <= DistFun(v)[w]
    BY <1>1 DEF Gossip, TypeOK, Safety, DistFun, vars
  <2>. QED  
    BY SumWeaklyMonotonic, MeasureType, MeasureTypePrime, Zenon
       DEF Distance, Measure
<1>2. CASE UNCHANGED vars
  BY <1>2, MeasureType DEF DistFun, Distance, Measure, vars
<1>. QED  BY <1>1, <1>2

\* A non-stuttering Gossip action decreases the measure.
LEMMA GossipDecreasesMeasure ==
  ASSUME TypeOK, TypeOK', Safety, Safety',
         <<\E n,o \in Node : Gossip(n,o)>>_vars
  PROVE  Measure' < Measure
<1>. PICK n \in Node, o \in Node : <<Gossip(n,o)>>_vars
  OBVIOUS
<1>1. PICK v \in Node : counter[o][v] < counter[n][v]
  BY DEF Gossip, vars, TypeOK
<1>2. DistFun(o)'[v] < DistFun(o)[v]
  BY <1>1 DEF Gossip, vars, TypeOK, Safety, DistFun
<1>. QED
  BY <1>2, GossipDoesntIncreaseMeasure, SumStronglyMonotonic,
     MeasureType, MeasureTypePrime, Zenon 
     DEF Distance, Measure

(***************************************************************************)
(* We now prove convergence for the tail of the behavior in which only     *)
(* Gossip actions may occur. For convenience, we define a TLA+             *)
(* specification characterizing this eventual behavior.                    *)
(***************************************************************************)

OGSpec ==
  /\ [](TypeOK /\ Safety)
  /\ [][\E n, o \in Node : Gossip(n,o)]_vars
  /\ [](\A n, o \in Node : WF_vars(Gossip(n,o)))

\* The following is the main liveness theorem. Its proof is quite tedious
\* because of a delicate interplay of predicate and temporal logic reasoning.
THEOREM OGLiveness == OGSpec => <>(\A n, o \in Node : counter[n] = counter[o])
<1>. DEFINE Q == \A n, o \in Node : counter[n] = counter[o]
            P(m) == Measure = m
            L(m) == [](P(m) => <>Q)
<1>1. ASSUME NEW m \in Nat,
             \* must explicitly "box" the following assumption,
             \* otherwise PTL reasoning fails below.
             [](\A k \in 0 .. (m-1) : OGSpec => L(k))
      PROVE  [](OGSpec => L(m))
  <2>. DEFINE OGNext == \E n, o \in Node : Gossip(n,o)
  <2>1. CASE m = 0
    <3>1. TypeOK /\ Safety /\ P(m) => Q
      BY <2>1, MeasureIsZero DEF TypeOK
    <3>. QED  BY <3>1, PTL DEF OGSpec
  <2>2. CASE m > 0
    <3>1. OGSpec => [](P(m) => [](\E k \in 0 .. m : P(k)))
      <4>1. TypeOK /\ Safety /\ P(m) => \E k \in 0 .. m : P(k)
        BY MeasureType
      <4>2. /\ TypeOK /\ Safety /\ TypeOK' /\ Safety' 
            /\ \E k \in 0 .. m : P(k)
            /\ [OGNext]_vars
            => (\E k \in 0 .. m : P(k))'
        BY MeasureTypePrime, GossipDoesntIncreaseMeasure
      <4>. QED  BY <4>1, <4>2, PTL DEF OGSpec
    <3>5. OGSpec => [](P(m) /\ <><<OGNext>>_vars => <> \E k \in 0 .. (m-1) : P(k))
      <4>1. /\ TypeOK /\ Safety /\ TypeOK' /\ Safety'
            /\ \E k \in 0 .. m : P(k)
            /\ <<OGNext>>_vars
            => (\E k \in 0 .. (m-1) : P(k))'
        BY MeasureTypePrime, GossipDecreasesMeasure
      <4>. QED  BY <3>1, <4>1, PTL DEF OGSpec
    <3>6. OGSpec => [](P(m) /\ [][~OGNext]_vars => <> \E k \in 0 .. (m-1) : P(k))
      <4>. DEFINE C(n,o) == counter[o][n] < counter[n][n]
      <4>1. OGSpec /\ [][~OGNext]_vars /\ P(m) => \E u,v \in Node : []C(u,v)
        <5>1. TypeOK /\ Safety /\ P(m) => \E u,v \in Node : C(u,v)
          <6>. SUFFICES ASSUME TypeOK, Safety, P(m)
                        PROVE  \E n,o \in Node : C(n,o)
            OBVIOUS
          <6>1. PICK a,b,c \in Node : counter[a][c] # counter[b][c]
            BY <2>2, MeasureType, MeasureIsZero
          <6>2. CASE counter[a][c] < counter[b][c]
            BY <6>1, <6>2 DEF Safety, TypeOK
          <6>3. CASE counter[b][c] < counter[a][c]
            BY <6>1, <6>3 DEF Safety, TypeOK
          <6>. QED  BY <6>1, <6>2, <6>3 DEF TypeOK
        <5>2. OGSpec /\ [][~OGNext]_vars /\ P(m) => \E u,v \in Node : C(u,v)
          BY <5>1, PTL DEF OGSpec
        <5>3. OGSpec /\ [][~OGNext]_vars => \A u,v \in Node : C(u,v) => []C(u,v)
          <6>. SUFFICES ASSUME NEW u \in Node, NEW v \in Node
                        PROVE  C(u,v) /\ [][OGNext]_vars /\ [][~OGNext]_vars => []C(u,v)
            BY DEF OGSpec
          <6>. C(u,v) /\ [OGNext]_vars /\ [~OGNext]_vars => C(u,v)'
            BY DEF vars
          <6>. QED  BY PTL
        <5>. QED  BY <5>2, <5>3
      <4>2. OGSpec /\ [](\E k \in 0 .. m : P(k)) /\ (\E u,v \in Node : []C(u,v))
            => <> \E k \in 0 .. (m-1) : P(k)
        <5>. SUFFICES 
               ASSUME NEW u \in Node, NEW v \in Node
               PROVE  OGSpec /\ [](\E k \in 0 .. m : P(k)) /\ []C(u,v)
                      => <> \E k \in 0 .. (m-1) : P(k)
          OBVIOUS
        <5>1. TypeOK /\ C(u,v) => ENABLED <<Gossip(u,v)>>_vars
          BY EnabledGossip
        <5>2. /\ TypeOK /\ TypeOK' /\ Safety /\ Safety'
              /\ \E k \in 0 .. m : P(k)
              /\ <<Gossip(u,v)>>_vars
              => (\E k \in 0 .. (m-1) : P(k))'
          BY MeasureTypePrime, GossipDecreasesMeasure
        <5>3. OGSpec => WF_vars(Gossip(u,v))
          <6>1. (\A n,o \in Node : WF_vars(Gossip(n,o))) => WF_vars(Gossip(u,v))
            OBVIOUS
          <6>. QED  BY <6>1, PTL DEF OGSpec
        <5>. QED  BY <5>1, <5>2, <5>3, PTL DEF OGSpec
      <4>. HIDE DEF OGNext, P, C
      <4>3. OGSpec /\ [][~OGNext]_vars /\ P(m) /\ [](\E k \in 0 .. m : P(k))
            => <>(\E k \in 0 .. (m-1) : P(k))
         BY <4>1, <4>2
      <4>. QED  BY <3>1, <4>3, PTL DEF OGSpec
    <3>7. OGSpec => [](P(m) =>  <> \E k \in 0 .. (m-1) : P(k))
      BY <3>5, <3>6, PTL
    <3>8. OGSpec => []((\E k \in 0 .. (m-1) : P(k)) => <>Q)
      <4>1. (\A k \in 0 .. (m-1) : OGSpec => L(k)) 
            => (OGSpec => [](\A k \in 0 .. (m-1) : P(k) => <>Q))
        OBVIOUS
      <4>2. (\A k \in 0 .. (m-1) : P(k) => <>Q) 
            => ((\E k \in 0 .. (m-1) : P(k)) => <>Q)
        OBVIOUS
      <4>. QED  BY <1>1, <4>1, <4>2, PTL
    <3>. QED  BY <3>7, <3>8, PTL
  <2>. QED  BY <2>1, <2>2
<1>. DEFINE S(m) == [](OGSpec => L(m))
\* The following step just commutes [] and \A in the assumption of <1>1
\* so that we can apply the induction theorem in the following step.
<1>2. ASSUME NEW m \in Nat,
             \A k \in 0 .. (m-1) : S(k)
      PROVE  S(m)
  BY <1>1
<1>3. \A m \in Nat : S(m)
  <2>. HIDE DEF S
  <2>. QED  BY <1>2, GeneralNatInduction, Isa
\* Now turn the outermost universal quantifier into an existential quantifier
\* on the left-hand side of the consequent.
<1>4. OGSpec => []((\E m \in Nat : P(m)) => <>Q)
  <2>1. (\A m \in Nat : P(m) => <> Q) => ((\E m \in Nat : P(m)) => <>Q)
    OBVIOUS
  <2>2. [](\A m \in Nat : P(m) => <> Q) => []((\E m \in Nat : P(m)) => <>Q)
    BY <2>1, PTL
  <2>3. ASSUME NEW m \in Nat
        PROVE  OGSpec => L(m)
    <3>1. S(m)
      BY <1>3
    <3>. QED  BY <3>1, PTL
  <2>. QED  BY <1>3, <2>2, <2>3
\* Clearly P(m) must hold for some natural number initially.
<1>5. OGSpec => \E m \in Nat : P(m)
  <2>. TypeOK /\ Safety => \E m \in Nat : P(m)
    BY MeasureType
  <2>. QED  BY PTL DEF OGSpec
<1>. QED  BY <1>4, <1>5, PTL

\* The final theorem is a simple corollary.
THEOREM Liveness == FairSpec => Convergence
<1>1. (\A n,o \in Node : WF_vars(Gossip(n,o))) =>
      [](\A n,o \in Node : WF_vars(Gossip(n,o)))
  \* Tedious proof of an "obvious" fact, due to interplay of first-order 
  \* and temporal reasoning. Could this be proved automatically?
  <2>1. ASSUME NEW n \in Node, NEW o \in Node
        PROVE  WF_vars(Gossip(n,o)) => []WF_vars(Gossip(n,o))
    BY PTL
  <2>. QED  BY <2>1, Isa
<1>. QED
  BY <1>1, TypeCorrect, Safe, OGLiveness, PTL 
     DEF FairSpec, OGSpec, Fairness, Convergence

=============================================================================

