--------------------------- MODULE EWD687a_proof ---------------------------
(***************************************************************************)
(* TLAPS proofs of the theorems stated in EWD687a.tla.                     *)
(***************************************************************************)
EXTENDS EWD687a, NaturalsInduction, FiniteSetTheorems, TLAPS

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorem 1: Spec => CountersConsistent                                   *)
(*                                                                         *)
(* The four counters per edge are always consistent: the number of         *)
(* messages ever sent on an edge equals the messages received and          *)
(* acknowledged plus the messages received and not yet acked plus the      *)
(* acks in flight plus the messages still in flight.                       *)
(*                                                                         *)
(* TypeOK on its own is not inductive: in RcvAck and SendAck a counter is  *)
(* decremented, and we can only show that the result stays in Nat by also  *)
(* knowing the counters are consistent.  We therefore prove TypeOK and the *)
(* state predicate Counters together as a single inductive invariant.     *)
(***************************************************************************)
Counters == \A e \in Edges : sentUnacked[e] = rcvdUnacked[e] + acks[e] + msgs[e]

Inv1 == TypeOK /\ Counters

LEMMA Inv1Init == Init => Inv1
BY DEF Init, Inv1, TypeOK, Counters, NotAnEdge

LEMMA Inv1Step == Inv1 /\ [Next]_vars => Inv1'
  <2> SUFFICES ASSUME Inv1, [Next]_vars
               PROVE  Inv1'
    OBVIOUS
  <2>. USE DEF Inv1, TypeOK, Counters
  <2>1. ASSUME NEW p \in Procs, SendMsg(p)
        PROVE  Inv1'
    BY <2>1 DEF SendMsg, OutEdges
  <2>2. ASSUME NEW p \in Procs, RcvAck(p)
        PROVE  Inv1'
    BY <2>2 DEF RcvAck, OutEdges
  <2>3. ASSUME NEW p \in Procs, SendAck(p)
        PROVE  Inv1'
    BY <2>3 DEF SendAck, InEdges, neutral
  <2>4. ASSUME NEW p \in Procs, RcvMsg(p)
        PROVE  Inv1'
    <3>1. PICK e \in InEdges(p) :
                /\ msgs[e] > 0
                /\ msgs' = [msgs EXCEPT ![e] = @ - 1]
                /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ + 1]
                /\ active' = [active EXCEPT ![p] = TRUE]
                /\ upEdge' = IF neutral(p) THEN [upEdge EXCEPT ![p] = e]
                                           ELSE upEdge
                /\ UNCHANGED <<acks, sentUnacked>>
      BY <2>4 DEF RcvMsg
    <3>2. p # Leader
      BY <3>1, EdgeFacts DEF InEdges
    <3>3. e[2] = p /\ e \in Edges
      BY <3>1 DEF InEdges
    <3>. QED
      BY <3>1, <3>2, <3>3 DEF InEdges, neutral, NotAnEdge
  <2>5. ASSUME NEW p \in Procs, Idle(p)
        PROVE  Inv1'
    BY <2>5 DEF Idle
  <2>6. CASE UNCHANGED vars
    BY <2>6 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next

LEMMA Inv1Inductive == Spec => []Inv1
BY Inv1Init, Inv1Step, PTL DEF Spec

THEOREM TypeCorrect == Spec => []TypeOK
BY Inv1Inductive, PTL DEF Inv1

THEOREM Thm_CountersConsistent == Spec => CountersConsistent
BY Inv1Inductive, PTL DEF CountersConsistent, Inv1, Counters

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorem 3: Spec => []DT1Inv                                             *)
(*                                                                         *)
(* Main safety property: when the leader is neutral, the entire            *)
(* computation has terminated, i.e., every non-leader process is also      *)
(* neutral.                                                                *)
(*                                                                         *)
(* DT1Inv is not directly inductive.  We strengthen it by adding two       *)
(* invariants describing the structure of the overlay tree:                *)
(*                                                                         *)
(*   - Non-neutral non-leader processes always have an upEdge (so they     *)
(*     are part of the overlay tree).                                      *)
(*   - If p is in the tree, then upEdge[p] is a well-formed incoming edge  *)
(*     of p, the edge has at least one unacknowledged message              *)
(*     (rcvdUnacked >= 1), and (the key fact for DT1Inv) the parent of p   *)
(*     in the overlay tree is itself non-neutral.                          *)
(*                                                                         *)
(* From the second invariant, the chain of upEdges from any non-neutral    *)
(* non-leader p consists of non-neutral processes, so the leader cannot    *)
(* be neutral whenever any other process is non-neutral.  Formalising the  *)
(* finite-chain argument needs Procs to be finite and a small amount of    *)
(* well-founded reasoning, factored out as a separate lemma.               *)
(***************************************************************************)
ASSUME ProcsFinite == IsFiniteSet(Procs)

InTree(p) == upEdge[p] # NotAnEdge

Inv2 == /\ \A p \in Procs \ {Leader} : ~neutral(p) => InTree(p)
        /\ \A p \in Procs \ {Leader} :
                InTree(p) =>
                    /\ upEdge[p] \in Edges
                    /\ upEdge[p][2] = p
                    /\ upEdge[p][1] \in Procs \ {p}
                    /\ rcvdUnacked[upEdge[p]] >= 1

(***************************************************************************)
(* The chain step.                                                         *)
(*                                                                         *)
(* Assume Inv2 and neutral(Leader).  Suppose, for contradiction, that      *)
(* S == {p \in Procs \ {Leader} : ~neutral(p)} is non-empty.               *)
(*                                                                         *)
(*  - Conjunct 3 of Inv2 gives InTree(p) for every p in S.                 *)
(*  - Conjunct 4 of Inv2 + Counters give sentUnacked[upEdge[p]] >= 1,      *)
(*    so the parent upEdge[p][1] is non-neutral.                           *)
(*  - Since neutral(Leader), the parent is not Leader, hence the parent    *)
(*    is itself in S.                                                      *)
(*                                                                         *)
(* So upEdge[_][1] defines a function f : S -> S with no fixed points.     *)
(* In any non-empty set such an f might still admit a cycle, so we need an *)
(* auxiliary invariant ruling out cycles in the upEdge graph.  We use the  *)
(* following formulation: there is no non-empty set of in-tree non-leader  *)
(* processes that is closed under taking the parent.  (Equivalently: every *)
(* in-tree process can reach the leader by following upEdge.)              *)
(*                                                                         *)
(* NoCycle is established inductively (NoCycleInductive below).  All       *)
(* actions other than RcvMsg either leave upEdge unchanged or, in the     *)
(* case of SendAck removing p from the tree, leave p with no children    *)
(* (its OutEdges are quiescent), so any putative new closed set would     *)
(* already have been a closed set in the previous state.  RcvMsg may     *)
(* attach a new process p to the tree with parent e[1]; if a closed set  *)
(* S' arose in the new state with p \in S', then by Counters and Inv2    *)
(* conjunct 4 no other in-tree process points to p (since p was neutral, *)
(* every OutEdge of p has sentUnacked = 0), so removing p from S' yields  *)
(* a smaller closed set in the previous state - contradicting the         *)
(* induction hypothesis.                                                   *)
(***************************************************************************)
NoCycle == \A S \in SUBSET (Procs \ {Leader}) :
              ~ (/\ S # {}
                 /\ \A q \in S : InTree(q) /\ upEdge[q][1] \in S)

LEMMA Inv2Inductive == Spec => []Inv2
<1>1. Init => Inv2
  <2>. SUFFICES ASSUME Init PROVE Inv2
    OBVIOUS
  <2>2. \A p \in Procs \ {Leader} : ~neutral(p) => InTree(p)
    BY DEF Init, neutral, InEdges, OutEdges
  <2>3. \A p \in Procs \ {Leader} : ~ InTree(p)
    BY DEF Init, InTree, NotAnEdge
  <2>. QED  BY <2>2, <2>3 DEF Inv2
<1>2. Inv1 /\ Inv1' /\ Inv2 /\ [Next]_vars => Inv2'
  <2> SUFFICES ASSUME Inv1, Inv1', Inv2, [Next]_vars
               PROVE  Inv2'
    OBVIOUS
  <2>. USE DEF Inv1, Inv2, TypeOK, Counters, InTree, NotAnEdge
  <2>1. ASSUME NEW p \in Procs, SendMsg(p)
        PROVE  Inv2'
    \* SendMsg only changes sentUnacked and msgs on one out-edge of p.
    \* It does not change active, rcvdUnacked, or upEdge.
    BY <2>1, EdgeFacts DEF SendMsg, OutEdges, InEdges, neutral
  <2>5. ASSUME NEW p \in Procs, Idle(p)
        PROVE  Inv2'
    \* Idle only changes active[p] to FALSE.  Counters and upEdge are
    \* unchanged.  Neutral status of any p' might switch from non-neutral
    \* to neutral, but the conjuncts of Inv2 are upper bounds, so they
    \* are preserved.
    BY <2>5, EdgeFacts DEF Idle, OutEdges, InEdges, neutral
  <2>6. CASE UNCHANGED vars
    BY <2>6 DEF vars, neutral, InEdges, OutEdges
  <2>2. ASSUME NEW p \in Procs, RcvAck(p)
        PROVE  Inv2'
    <3>1. PICK e \in OutEdges(p) :
                /\ acks[e] > 0
                /\ acks' = [acks EXCEPT ![e] = @ - 1]
                /\ sentUnacked' = [sentUnacked EXCEPT ![e] = @ - 1]
                /\ UNCHANGED <<active, msgs, rcvdUnacked, upEdge>>
      BY <2>2 DEF RcvAck
    <3>2. e \in Edges /\ e[1] = p /\ e[1] # e[2] /\ e[2] \in Procs \ {p}
      BY <3>1, EdgeFacts DEF OutEdges
    \* Only sentUnacked and acks for e change.  active, rcvdUnacked, msgs,
    \* and upEdge are unchanged.  The neutrality of any q with q # p is
    \* unaffected (sentUnacked, acks change only on edges in OutEdges(p)).
    <3>3. \A q \in Procs : q # p => (neutral(q) <=> neutral(q)')
      BY <3>1, <3>2 DEF neutral, OutEdges, InEdges
    \* For p, the new sentUnacked[e] is one less; if that makes p neutral,
    \* the conjunct "non-neutral implies InTree" still holds (vacuously
    \* for p) since others' status is preserved.
    <3>4. \A q \in Procs \ {Leader} : ~ neutral(q)' => InTree(q)'
      <4>1. SUFFICES ASSUME NEW q \in Procs \ {Leader}, ~ neutral(q)'
                     PROVE  InTree(q)'
        OBVIOUS
      <4>2. CASE q = p
        \* upEdge unchanged, so InTree(p)' = InTree(p).  Need ~neutral(p).
        \* If neutral(p) before, then sentUnacked[e] = 0 (since e \in
        \* OutEdges(p)).  By Counters, acks[e] = 0, contradicting <3>1.
        <5>1. ~ neutral(p)
          <6>1. SUFFICES ASSUME neutral(p) PROVE FALSE
            OBVIOUS
          <6>2. sentUnacked[e] = 0
            BY <3>2, <6>1 DEF neutral
          <6>3. acks[e] = 0
            BY <3>2, <6>2 DEF Counters
          <6>4. acks[e] > 0
            BY <3>1
          <6>. QED  BY <6>3, <6>4
        <5>2. InTree(p)
          BY <4>2, <5>1
        <5>3. upEdge'[p] = upEdge[p]
          BY <3>1
        <5>. QED  BY <4>2, <5>2, <5>3
      <4>3. CASE q # p
        <5>1. ~ neutral(q)
          BY <3>3, <4>3, <4>1
        <5>2. InTree(q)
          BY <5>1
        <5>3. upEdge'[q] = upEdge[q]
          BY <3>1
        <5>. QED  BY <5>2, <5>3
      <4>. QED  BY <4>2, <4>3
    <3>5. \A q \in Procs \ {Leader} :
            InTree(q)' =>
                /\ upEdge'[q] \in Edges
                /\ upEdge'[q][2] = q
                /\ upEdge'[q][1] \in Procs \ {q}
                /\ rcvdUnacked'[upEdge'[q]] >= 1
      <4>1. SUFFICES ASSUME NEW q \in Procs \ {Leader}, InTree(q)'
                     PROVE /\ upEdge'[q] \in Edges
                           /\ upEdge'[q][2] = q
                           /\ upEdge'[q][1] \in Procs \ {q}
                           /\ rcvdUnacked'[upEdge'[q]] >= 1
        OBVIOUS
      <4>2. upEdge'[q] = upEdge[q]
        BY <3>1
      <4>3. InTree(q)
        BY <4>1, <4>2
      <4>4. /\ upEdge[q] \in Edges
            /\ upEdge[q][2] = q
            /\ upEdge[q][1] \in Procs \ {q}
            /\ rcvdUnacked[upEdge[q]] >= 1
        BY <4>3
      <4>5. rcvdUnacked'[upEdge[q]] = rcvdUnacked[upEdge[q]]
        BY <3>1
      <4>. QED  BY <4>2, <4>4, <4>5
    <3>. QED  BY <3>4, <3>5 DEF Inv2
  <2>3. ASSUME NEW p \in Procs, SendAck(p)
        PROVE  Inv2'
    <3>1. PICK e \in InEdges(p) :
                /\ rcvdUnacked[e] > 0
                /\ (e = upEdge[p]) =>
                    \/ rcvdUnacked[e] > 1
                    \/ /\ ~ active[p]
                       /\ \A d \in InEdges(p) \ {e} : rcvdUnacked[d] = 0
                       /\ \A d \in OutEdges(p) : sentUnacked[d] = 0
                /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ - 1]
                /\ acks' = [acks EXCEPT ![e] = @ + 1]
      BY <2>3 DEF SendAck
    <3>2. /\ UNCHANGED <<active, msgs, sentUnacked>>
          /\ upEdge' = IF neutral(p)' THEN [upEdge EXCEPT ![p] = NotAnEdge]
                                      ELSE upEdge
      BY <2>3 DEF SendAck
    <3>3a. e \in Edges /\ e[2] = p /\ e \in Procs \X Procs /\ e[1] # e[2]
      BY <3>1, EdgeFacts DEF InEdges
    <3>3b. p # Leader
      <4>1. SUFFICES ASSUME p = Leader PROVE FALSE
        OBVIOUS
      <4>2. e \in InEdges(Leader)
        BY <3>1, <4>1
      <4>3. InEdges(Leader) = {}
        BY EdgeFacts
      <4>. QED  BY <4>2, <4>3
    <3>3. p \in Procs \ {Leader} /\ e \in Edges /\ e[2] = p /\ e[1] # p /\ e[1] \in Procs
      BY <3>3a, <3>3b
    \* For q # p, neutrality is unchanged (rcvdUnacked, acks change only on
    \* edge e in InEdges(p), so for q # p, no relevant counters change).
    <3>4. \A q \in Procs : q # p => (neutral(q) <=> neutral(q)')
      BY <3>1, <3>2, <3>3 DEF neutral, OutEdges, InEdges
    \* Conjunct 3 of Inv2.
    <3>5. \A q \in Procs \ {Leader} : ~ neutral(q)' => InTree(q)'
      <4>1. SUFFICES ASSUME NEW q \in Procs \ {Leader}, ~ neutral(q)'
                     PROVE  InTree(q)'
        OBVIOUS
      <4>2. CASE q = p
        \* If neutral'(p) holds, ~ neutral(p)' is false; trivial.
        \* Otherwise, upEdge' = upEdge.  We must show p was non-neutral
        \* before, hence upEdge[p] # NotAnEdge (i.e., InTree(p)).
        <5>1. ~ neutral(p)
          \* p was non-neutral because rcvdUnacked[e] > 0 with e \in
          \* InEdges(p), so the conjunct rcvdUnacked = 0 of neutral fails.
          BY <3>1, <3>3 DEF neutral
        <5>2. InTree(p)
          BY <4>2, <5>1
        <5>3. ~ neutral(p)'
          BY <4>1, <4>2
        <5>4. upEdge'[p] = upEdge[p]
          BY <3>2, <5>3
        <5>. QED  BY <4>2, <5>2, <5>4
      <4>3. CASE q # p
        <5>1. ~ neutral(q)
          BY <3>4, <4>3, <4>1
        <5>2. InTree(q)
          BY <5>1
        <5>3. upEdge'[q] = upEdge[q]
          \* upEdge'[q] = upEdge[q] regardless of the conditional, since
          \* the conditional only changes upEdge[p].
          BY <3>2, <4>3
        <5>. QED  BY <5>2, <5>3
      <4>. QED  BY <4>2, <4>3
    \* Conjunct 4 of Inv2.
    <3>6. \A q \in Procs \ {Leader} :
            InTree(q)' =>
                /\ upEdge'[q] \in Edges
                /\ upEdge'[q][2] = q
                /\ upEdge'[q][1] \in Procs \ {q}
                /\ rcvdUnacked'[upEdge'[q]] >= 1
      <4>1. SUFFICES ASSUME NEW q \in Procs \ {Leader}, InTree(q)'
                     PROVE /\ upEdge'[q] \in Edges
                           /\ upEdge'[q][2] = q
                           /\ upEdge'[q][1] \in Procs \ {q}
                           /\ rcvdUnacked'[upEdge'[q]] >= 1
        OBVIOUS
      <4>2. CASE q = p
        \* InTree(p)' implies upEdge'[p] # NotAnEdge.  By <3>2, this means
        \* either ~neutral'(p) and upEdge unchanged for p, or neutral'(p)
        \* and upEdge'[p] = NotAnEdge (contradicting InTree(p)').
        <5>1. ~ neutral(p)'
          BY <4>1, <4>2, <3>2, <3>3 DEF NotAnEdge
        <5>2. upEdge'[p] = upEdge[p]
          BY <3>2, <5>1
        <5>3. InTree(p)
          BY <4>1, <4>2, <5>2
        <5>4. /\ upEdge[p] \in Edges
              /\ upEdge[p][2] = p
              /\ upEdge[p][1] \in Procs \ {p}
              /\ rcvdUnacked[upEdge[p]] >= 1
          BY <5>3, <3>3
        \* For the rcvdUnacked' >= 1 part:
        \*  - If upEdge[p] # e (the SendAck edge), then rcvdUnacked' is
        \*    unchanged at upEdge[p].
        \*  - If upEdge[p] = e, then SendAck's case-2a/2b applies: either
        \*    rcvdUnacked[e] > 1 (so rcvdUnacked' >= 1), or neutral'(p)
        \*    holds, contradicting <5>1.
        <5>5. rcvdUnacked'[upEdge[p]] >= 1
          <6>1. CASE upEdge[p] # e
            BY <3>1, <5>4, <6>1
          <6>2. CASE upEdge[p] = e
            <7>1. CASE rcvdUnacked[e] > 1
              \* rcvdUnacked'[e] = rcvdUnacked[e] - 1 >= 1.
              BY <3>1, <3>3, <5>4, <6>2, <7>1
            <7>2. CASE ~ rcvdUnacked[e] > 1
              \* Then rcvdUnacked[e] = 1 (since rcvdUnacked[e] > 0).
              \* From SendAck precondition (since case 2a fails), case 2b
              \* must hold: ~active[p] /\ all other rcvdUnacked = 0 /\ all
              \* sentUnacked = 0 on OutEdges(p).  Combined with
              \* rcvdUnacked'[e] = 0, we obtain neutral'(p), contradicting
              \* ~neutral'(p).
              <8>0. rcvdUnacked[e] = 1
                BY <3>1, <3>3, <7>2 DEF Counters, TypeOK
              <8>1. /\ ~active[p]
                    /\ \A d \in InEdges(p) \ {e} : rcvdUnacked[d] = 0
                    /\ \A d \in OutEdges(p) : sentUnacked[d] = 0
                BY <3>1, <6>2, <7>2
              <8>2. rcvdUnacked'[e] = 0
                BY <3>1, <3>3, <8>0
              <8>3. \A d \in InEdges(p) : rcvdUnacked'[d] = 0
                <9>1. SUFFICES ASSUME NEW d \in InEdges(p)
                               PROVE  rcvdUnacked'[d] = 0
                  OBVIOUS
                <9>2. CASE d = e
                  BY <8>2, <9>2
                <9>3. CASE d # e
                  <10>1. rcvdUnacked'[d] = rcvdUnacked[d]
                    BY <3>1, <9>1, <9>3 DEF InEdges
                  <10>2. rcvdUnacked[d] = 0
                    BY <8>1, <9>1, <9>3
                  <10>. QED  BY <10>1, <10>2
                <9>. QED  BY <9>2, <9>3
              <8>4. \A d \in OutEdges(p) : sentUnacked'[d] = 0
                BY <3>2, <8>1
              <8>5. ~active[p]'
                BY <3>2, <8>1
              <8>6. neutral(p)'
                BY <8>3, <8>4, <8>5 DEF neutral
              <8>. QED  BY <8>6, <5>1
            <7>. QED  BY <7>1, <7>2
          <6>. QED  BY <6>1, <6>2
        <5>. QED  BY <4>2, <5>2, <5>4, <5>5
      <4>3. CASE q # p
        <5>1. upEdge'[q] = upEdge[q]
          BY <3>2, <4>3
        <5>2. InTree(q)
          BY <4>1, <5>1
        <5>3. /\ upEdge[q] \in Edges
              /\ upEdge[q][2] = q
              /\ upEdge[q][1] \in Procs \ {q}
              /\ rcvdUnacked[upEdge[q]] >= 1
          BY <5>2
        \* upEdge[q][2] = q and e[2] = p (from <3>3), with q # p,
        \* so upEdge[q] # e.  Hence rcvdUnacked' is unchanged at upEdge[q].
        <5>4. upEdge[q] # e
          BY <3>3, <4>3, <5>3
        <5>5. rcvdUnacked'[upEdge[q]] = rcvdUnacked[upEdge[q]]
          BY <3>1, <5>3, <5>4
        <5>. QED  BY <5>1, <5>3, <5>5
      <4>. QED  BY <4>2, <4>3
    <3>. QED  BY <3>5, <3>6 DEF Inv2
  <2>4. ASSUME NEW p \in Procs, RcvMsg(p)
        PROVE  Inv2'
    <3>1. PICK e \in InEdges(p) :
                /\ msgs[e] > 0
                /\ msgs' = [msgs EXCEPT ![e] = @ - 1]
                /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ + 1]
                /\ active' = [active EXCEPT ![p] = TRUE]
                /\ upEdge' = IF neutral(p) THEN [upEdge EXCEPT ![p] = e]
                                           ELSE upEdge
                /\ UNCHANGED <<acks, sentUnacked>>
      BY <2>4 DEF RcvMsg
    <3>2. p \in Procs \ {Leader} /\ e \in Edges /\ e[2] = p /\ e[1] # p /\ e[1] \in Procs
      BY <3>1, EdgeFacts DEF InEdges
    \* Active'[p] = TRUE, hence ~neutral'(p) (due to active flag).
    \* For q # p, neutrality status is unchanged by RcvMsg(p).
    <3>3. \A q \in Procs : q # p => (neutral(q) <=> neutral(q)')
      BY <3>1, <3>2 DEF neutral, InEdges, OutEdges
    <3>4. ~ (neutral(p))'
      BY <3>1, <3>2 DEF neutral
    <3>5. \A q \in Procs \ {Leader} : ~ neutral(q)' => InTree(q)'
      <4>1. SUFFICES ASSUME NEW q \in Procs \ {Leader}, ~ neutral(q)'
                     PROVE  InTree(q)'
        OBVIOUS
      <4>2. CASE q = p
        \* If p was neutral, upEdge' is set to e, so InTree'(p).
        \* If p was non-neutral, upEdge' = upEdge and we use the IH.
        <5>1. CASE neutral(p)
          \* upEdge'[p] = e \in Edges, e \in Procs \X Procs, so e is a
          \* 2-tuple, hence e # NotAnEdge = <<>>.
          <6>1. upEdge'[p] = e
            BY <3>1, <3>2, <5>1
          <6>2. e \in Procs \X Procs
            BY <3>2, EdgeFacts
          <6>3. e # NotAnEdge
            BY <6>2 DEF NotAnEdge
          <6>. QED  BY <4>2, <6>1, <6>3
        <5>2. CASE ~neutral(p)
          <6>1. InTree(p)
            BY <5>2, <3>2
          <6>2. upEdge'[p] = upEdge[p]
            BY <3>1, <5>2
          <6>. QED  BY <4>2, <6>1, <6>2
        <5>. QED  BY <5>1, <5>2
      <4>3. CASE q # p
        <5>1. ~neutral(q)
          BY <3>3, <4>3, <4>1
        <5>2. InTree(q)
          BY <5>1
        <5>3. upEdge'[q] = upEdge[q]
          BY <3>1, <4>3
        <5>. QED  BY <5>2, <5>3
      <4>. QED  BY <4>2, <4>3
    <3>6. \A q \in Procs \ {Leader} :
            InTree(q)' =>
                /\ upEdge'[q] \in Edges
                /\ upEdge'[q][2] = q
                /\ upEdge'[q][1] \in Procs \ {q}
                /\ rcvdUnacked'[upEdge'[q]] >= 1
      <4>1. SUFFICES ASSUME NEW q \in Procs \ {Leader}, InTree(q)'
                     PROVE /\ upEdge'[q] \in Edges
                           /\ upEdge'[q][2] = q
                           /\ upEdge'[q][1] \in Procs \ {q}
                           /\ rcvdUnacked'[upEdge'[q]] >= 1
        OBVIOUS
      <4>2. CASE q = p
        <5>1. CASE neutral(p)
          \* upEdge'[p] = e, e[2] = p, e \in Edges, e[1] \in Procs \ {p}.
          \* rcvdUnacked'[e] = rcvdUnacked[e] + 1 >= 1.
          BY <3>1, <3>2, <4>2, <5>1
        <5>2. CASE ~neutral(p)
          \* upEdge'[p] = upEdge[p], use IH for p.
          <6>1. InTree(p)
            BY <5>2, <3>2
          <6>2. upEdge'[p] = upEdge[p]
            BY <3>1, <5>2
          <6>3. /\ upEdge[p] \in Edges
                /\ upEdge[p][2] = p
                /\ upEdge[p][1] \in Procs \ {p}
                /\ rcvdUnacked[upEdge[p]] >= 1
            BY <6>1, <3>2
          \* Either upEdge[p] = e (then rcvdUnacked' = rcvdUnacked+1 >= 2)
          \* or upEdge[p] # e (then rcvdUnacked'[upEdge[p]] = rcvdUnacked[upEdge[p]]).
          <6>4. rcvdUnacked'[upEdge[p]] >= 1
            BY <3>1, <6>3
          <6>. QED  BY <4>2, <6>2, <6>3, <6>4
        <5>. QED  BY <5>1, <5>2
      <4>3. CASE q # p
        \* upEdge'[q] = upEdge[q].  Neutrality of q unchanged.
        <5>1. upEdge'[q] = upEdge[q]
          BY <3>1, <4>3
        <5>2. InTree(q)
          BY <4>1, <5>1
        <5>3. /\ upEdge[q] \in Edges
              /\ upEdge[q][2] = q
              /\ upEdge[q][1] \in Procs \ {q}
              /\ rcvdUnacked[upEdge[q]] >= 1
          BY <5>2
        \* upEdge[q][2] = q and e[2] = p, with q # p, so upEdge[q] # e.
        <5>4. upEdge[q] # e
          BY <3>2, <4>3, <5>3
        <5>5. rcvdUnacked'[upEdge[q]] = rcvdUnacked[upEdge[q]]
          BY <3>1, <5>3, <5>4
        <5>. QED  BY <5>1, <5>3, <5>5
      <4>. QED  BY <4>2, <4>3
    <3>. QED  BY <3>5, <3>6 DEF Inv2
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
<1>. QED  BY <1>1, <1>2, Inv1Inductive, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Inductiveness of the auxiliary acyclicity invariant NoCycle (defined    *)
(* alongside Inv2 above).  The proof depends on Inv2 (in particular        *)
(* Counters and conjunct 4) for the RcvMsg case.                           *)
(***************************************************************************)
LEMMA NoCycleInit == Init => NoCycle
  <1>. SUFFICES ASSUME Init,
                       NEW S \in SUBSET (Procs \ {Leader}),
                       S # {},
                       \A q \in S : InTree(q) /\ upEdge[q][1] \in S
                PROVE  FALSE
    BY DEF NoCycle
  <1>1. PICK q \in S : TRUE
    OBVIOUS
  <1>2. q \in Procs \ {Leader}
    OBVIOUS
  <1>3. upEdge[q] = NotAnEdge
    BY <1>2 DEF Init
  <1>4. ~ InTree(q)
    BY <1>3 DEF InTree
  <1>. QED  BY <1>1, <1>4

LEMMA NoCycleStep == Inv1 /\ Inv2 /\ NoCycle /\ [Next]_vars => NoCycle'
  <1>. SUFFICES ASSUME Inv1, Inv2, NoCycle, [Next]_vars
                PROVE  NoCycle'
    OBVIOUS
  <1>. USE DEF Inv1, Inv2, TypeOK, Counters, InTree, NotAnEdge
  <1>1. ASSUME NEW p \in Procs, SendMsg(p)
        PROVE  NoCycle'
    <2>1. upEdge' = upEdge
      BY <1>1 DEF SendMsg
    <2>. SUFFICES ASSUME NEW S \in SUBSET (Procs \ {Leader}),
                          S # {},
                          \A q \in S : InTree(q)' /\ upEdge'[q][1] \in S
                  PROVE  FALSE
      BY DEF NoCycle
    <2>. QED  BY <2>1 DEF NoCycle
  <1>2. ASSUME NEW p \in Procs, RcvAck(p)
        PROVE  NoCycle'
    <2>1. upEdge' = upEdge
      BY <1>2 DEF RcvAck
    <2>. SUFFICES ASSUME NEW S \in SUBSET (Procs \ {Leader}),
                          S # {},
                          \A q \in S : InTree(q)' /\ upEdge'[q][1] \in S
                  PROVE  FALSE
      BY DEF NoCycle
    <2>. QED  BY <2>1 DEF NoCycle
  <1>3. ASSUME NEW p \in Procs, Idle(p)
        PROVE  NoCycle'
    <2>1. upEdge' = upEdge
      BY <1>3 DEF Idle
    <2>. SUFFICES ASSUME NEW S \in SUBSET (Procs \ {Leader}),
                          S # {},
                          \A q \in S : InTree(q)' /\ upEdge'[q][1] \in S
                  PROVE  FALSE
      BY DEF NoCycle
    <2>. QED  BY <2>1 DEF NoCycle
  <1>4. CASE UNCHANGED vars
    <2>1. upEdge' = upEdge
      BY <1>4 DEF vars
    <2>. SUFFICES ASSUME NEW S \in SUBSET (Procs \ {Leader}),
                          S # {},
                          \A q \in S : InTree(q)' /\ upEdge'[q][1] \in S
                  PROVE  FALSE
      BY DEF NoCycle
    <2>. QED  BY <2>1 DEF NoCycle
  <1>5. ASSUME NEW p \in Procs, SendAck(p)
        PROVE  NoCycle'
    <2>0. PICK e \in InEdges(p) :
                /\ rcvdUnacked[e] > 0
                /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ - 1]
                /\ acks' = [acks EXCEPT ![e] = @ + 1]
      BY <1>5 DEF SendAck
    <2>1. upEdge' = IF neutral(p)' THEN [upEdge EXCEPT ![p] = NotAnEdge]
                                   ELSE upEdge
      BY <1>5 DEF SendAck
    <2>2. p # Leader
      <3>1. SUFFICES ASSUME p = Leader PROVE FALSE
        OBVIOUS
      <3>2. e \in InEdges(Leader)
        BY <2>0, <3>1
      <3>3. InEdges(Leader) = {}
        BY EdgeFacts
      <3>. QED  BY <3>2, <3>3
    <2>. SUFFICES ASSUME NEW S \in SUBSET (Procs \ {Leader}),
                          S # {},
                          \A q \in S : InTree(q)' /\ upEdge'[q][1] \in S
                  PROVE  FALSE
      BY DEF NoCycle
    <2>case1. CASE ~ neutral(p)'
      <3>1. upEdge' = upEdge
        BY <2>1, <2>case1
      <3>2. \A q \in S : InTree(q) /\ upEdge[q][1] \in S
        BY <3>1
      <3>. QED  BY <3>2 DEF NoCycle
    <2>case2. CASE neutral(p)'
      <3>1. upEdge' = [upEdge EXCEPT ![p] = NotAnEdge]
        BY <2>1, <2>case2
      <3>2. p \in DOMAIN upEdge
        BY <2>2
      <3>3. upEdge'[p] = NotAnEdge
        BY <3>1, <3>2
      <3>4. ~ InTree(p)'
        BY <3>3
      <3>5. p \notin S
        BY <3>4
      <3>6. \A q \in S : q # p
        BY <3>5
      <3>7. \A q \in S : upEdge'[q] = upEdge[q]
        BY <3>1, <3>6
      <3>8. \A q \in S : InTree(q) /\ upEdge[q][1] \in S
        BY <3>7
      <3>. QED  BY <3>8 DEF NoCycle
    <2>. QED  BY <2>case1, <2>case2
  <1>6. ASSUME NEW p \in Procs, RcvMsg(p)
        PROVE  NoCycle'
    <2>0. PICK e \in InEdges(p) :
                /\ msgs[e] > 0
                /\ msgs' = [msgs EXCEPT ![e] = @ - 1]
                /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ + 1]
                /\ active' = [active EXCEPT ![p] = TRUE]
                /\ upEdge' = IF neutral(p) THEN [upEdge EXCEPT ![p] = e]
                                           ELSE upEdge
                /\ UNCHANGED <<acks, sentUnacked>>
      BY <1>6 DEF RcvMsg
    <2>1. p \in Procs \ {Leader} /\ e \in Edges /\ e[2] = p /\ e[1] # p /\ e[1] \in Procs
      BY <2>0, EdgeFacts DEF InEdges
    <2>. SUFFICES ASSUME NEW S \in SUBSET (Procs \ {Leader}),
                          S # {},
                          \A q \in S : InTree(q)' /\ upEdge'[q][1] \in S
                  PROVE  FALSE
      BY DEF NoCycle
    <2>case1. CASE ~ neutral(p)
      <3>1. upEdge' = upEdge
        BY <2>0, <2>case1
      <3>2. \A q \in S : InTree(q) /\ upEdge[q][1] \in S
        BY <3>1
      <3>. QED  BY <3>2 DEF NoCycle
    <2>case2. CASE neutral(p)
      <3>1. upEdge' = [upEdge EXCEPT ![p] = e]
        BY <2>0, <2>case2
      <3>2. p \in DOMAIN upEdge
        BY <2>1
      <3>caseA. CASE p \notin S
        <4>1. \A q \in S : q # p
          BY <3>caseA
        <4>2. \A q \in S : upEdge'[q] = upEdge[q]
          BY <3>1, <4>1
        <4>3. \A q \in S : InTree(q) /\ upEdge[q][1] \in S
          BY <4>2
        <4>. QED  BY <4>3 DEF NoCycle
      <3>caseB. CASE p \in S
        <4>0. upEdge'[p] = e
          BY <3>1, <3>2
        <4>1. upEdge'[p][1] = e[1]
          BY <4>0
        <4>2. e[1] \in S
          BY <3>caseB, <4>1
        <4>3. e[1] # p
          BY <2>1
        <4>4. e[1] \in S \ {p}
          BY <4>2, <4>3
        <4>5. SUFFICES ASSUME NEW q \in S \ {p}
                       PROVE  InTree(q) /\ upEdge[q][1] \in (S \ {p})
          BY <4>4 DEF NoCycle
        <4>9. q \in S /\ q # p /\ q \in Procs \ {Leader}
          OBVIOUS
        <4>11. upEdge'[q] = upEdge[q]
          BY <3>1, <4>9
        <4>12. InTree(q)
          BY <4>9, <4>11
        <4>13. upEdge[q][1] \in S
          BY <4>9, <4>11
        <4>14. /\ upEdge[q] \in Edges
               /\ upEdge[q][2] = q
               /\ upEdge[q][1] \in Procs \ {q}
               /\ rcvdUnacked[upEdge[q]] >= 1
          BY <4>9, <4>12
        <4>15. sentUnacked[upEdge[q]] >= 1
          BY <4>14
        <4>16. upEdge[q][1] # p
          <5>1. SUFFICES ASSUME upEdge[q][1] = p PROVE FALSE
            OBVIOUS
          <5>2. upEdge[q] \in OutEdges(p)
            BY <5>1, <4>14 DEF OutEdges
          <5>3. sentUnacked[upEdge[q]] = 0
            BY <2>case2, <5>2 DEF neutral
          <5>. QED  BY <4>15, <5>3
        <4>17. upEdge[q][1] \in (S \ {p})
          BY <4>13, <4>16
        <4>. QED  BY <4>12, <4>17
      <3>. QED  BY <3>caseA, <3>caseB
    <2>. QED  BY <2>case1, <2>case2
  <1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

LEMMA NoCycleInductive == Spec => []NoCycle
  <1>1. Init => NoCycle
    BY NoCycleInit
  <1>2. Inv1 /\ Inv2 /\ NoCycle /\ [Next]_vars => NoCycle'
    BY NoCycleStep
  <1>3. Spec => []Inv2
    BY Inv2Inductive
  <1>4. Spec => []Inv1
    BY Inv1Inductive
  <1>. QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec

(***************************************************************************)
(* Discharge of DT1FromInv2 using Inv2 and the acyclicity invariant.       *)
(***************************************************************************)
LEMMA DT1FromInv2 == Inv1 /\ Inv2 /\ NoCycle => DT1Inv
  <1>. SUFFICES ASSUME Inv1, Inv2, NoCycle PROVE DT1Inv
    OBVIOUS
  <1>. USE DEF Inv1, Inv2, TypeOK, Counters, InTree, NotAnEdge
  <1>. SUFFICES ASSUME neutral(Leader),
                       NEW p0 \in Procs \ {Leader}
                PROVE  neutral(p0)
    BY DEF DT1Inv
  <1>contra. ASSUME ~ neutral(p0) PROVE FALSE
    <2>. DEFINE S == {q \in Procs \ {Leader} : ~ neutral(q)}
    <2>4. S # {}
      BY <1>contra DEF S
    <2>5. S \in SUBSET (Procs \ {Leader})
      BY DEF S
    <2>6. SUFFICES ASSUME NEW q \in S
                    PROVE  InTree(q) /\ upEdge[q][1] \in S
      BY <2>4, <2>5 DEF NoCycle
    <2>8. q \in Procs \ {Leader} /\ ~ neutral(q)
      BY DEF S
    <2>9. InTree(q)
      BY <2>8
    <2>10. /\ upEdge[q] \in Edges
           /\ upEdge[q][2] = q
           /\ upEdge[q][1] \in Procs \ {q}
           /\ rcvdUnacked[upEdge[q]] >= 1
      BY <2>8, <2>9
    <2>11. sentUnacked[upEdge[q]] >= 1
      BY <2>10
    <2>12. upEdge[q] \in OutEdges(upEdge[q][1])
      BY <2>10 DEF OutEdges
    <2>13. ~ neutral(upEdge[q][1])
      BY <2>11, <2>12 DEF neutral
    <2>16. upEdge[q][1] \in S
      BY <2>10, <2>13 DEF S
    <2>. QED  BY <2>9, <2>16
  <1>. QED  BY <1>contra

THEOREM Thm_DT1Inv == Spec => []DT1Inv
  <1>0. Spec => []Inv1
    BY Inv1Inductive
  <1>1. Spec => []Inv2
    BY Inv2Inductive
  <1>2. Spec => []NoCycle
    BY NoCycleInductive
  <1>3. Inv1 /\ Inv2 /\ NoCycle => DT1Inv
    BY DT1FromInv2
  <1>. QED
    BY <1>0, <1>1, <1>2, <1>3, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorem 2: Spec => TreeWithRoot                                         *)
(*                                                                         *)
(* The set E of upEdges (excluding NotAnEdge), with N the set of nodes     *)
(* appearing in those edges, forms (when transposed) a tree rooted at      *)
(* the leader, and every node of that tree is non-neutral.                 *)
(*                                                                         *)
(* The structural invariants Inv2 + NoCycle proven above already capture   *)
(* the tree shape; what's left is to relate them to the                    *)
(* IsTreeWithRoot/AreConnectedIn predicates from the community-modules     *)
(* Graphs module.  For the connectivity part, we construct a simple path   *)
(* from each node to the leader by iterating upEdge.                       *)
(***************************************************************************)
G == INSTANCE Graphs

(***************************************************************************)
(* Concrete in-tree structure (the transposed overlay tree).               *)
(***************************************************************************)
EE == {upEdge[p] : p \in DOMAIN upEdge} \ {NotAnEdge}
NN == {e[1] : e \in EE} \cup {e[2] : e \in EE}
OO == G!Transpose([edge |-> EE, node |-> NN])

(***************************************************************************)
(* Both endpoints of every E-edge are non-neutral.  Children are           *)
(* non-neutral by Inv2 (InTree implies they are in the tree, hence         *)
(* non-neutral); parents are non-neutral because the tree edge has         *)
(* rcvdUnacked >= 1, so by Counters sentUnacked >= 1 and the parent       *)
(* fails the neutral predicate.                                            *)
(***************************************************************************)
LEMMA TreeNodesNonNeutral ==
  ASSUME Inv1, Inv2
  PROVE  \A n \in NN : ~ neutral(n)
  <1>. USE DEF Inv1, Inv2, TypeOK, Counters, InTree, NotAnEdge, NN, EE
  <1>. SUFFICES ASSUME NEW n \in NN
                PROVE  ~ neutral(n)
    OBVIOUS
  <1>1. PICK e \in EE : n = e[1] \/ n = e[2]
    OBVIOUS
  <1>2. PICK p \in DOMAIN upEdge : upEdge[p] = e /\ e # NotAnEdge
    OBVIOUS
  <1>3. p \in Procs \ {Leader}
    OBVIOUS
  <1>4. InTree(p)
    BY <1>2
  <1>5. /\ upEdge[p] \in Edges
        /\ upEdge[p][2] = p
        /\ upEdge[p][1] \in Procs \ {p}
        /\ rcvdUnacked[upEdge[p]] >= 1
    BY <1>3, <1>4
  <1>6. e \in Edges /\ e[2] = p /\ e[1] \in Procs \ {p}
    BY <1>2, <1>5
  <1>7. rcvdUnacked[e] >= 1
    BY <1>2, <1>5
  <1>8. sentUnacked[e] = rcvdUnacked[e] + acks[e] + msgs[e]
    BY <1>6
  <1>9. sentUnacked[e] >= 1
    BY <1>7, <1>8
  <1>10. e \in OutEdges(e[1]) /\ e \in InEdges(e[2])
    BY <1>6 DEF OutEdges, InEdges
  <1>11. ~ neutral(e[1])
    BY <1>9, <1>10 DEF neutral
  <1>12. ~ neutral(e[2])
    BY <1>7, <1>10 DEF neutral
  <1>. QED  BY <1>1, <1>11, <1>12

(***************************************************************************)
(* Tree-structural facts about OO derived from Inv2.                       *)
(***************************************************************************)
LEMMA TreeStructure ==
  ASSUME Inv1, Inv2
  PROVE  /\ OO.edge \subseteq NN \X NN
         /\ OO.node = NN
         /\ \A e \in OO.edge : e[1] # Leader
         /\ \A e \in OO.edge :
              \A f \in OO.edge : (e[1] = f[1]) => (e = f)
  <1>. USE DEF Inv1, Inv2, TypeOK, Counters, InTree, NotAnEdge,
              EE, NN, OO, G!Transpose
  <1>1. OO.edge \subseteq NN \X NN
    \* Each OO-edge is <<e[2], e[1]>> for some e \in EE.  For e \in EE,
    \* e[1] \in NN and e[2] \in NN (definition of NN).
    <2>. SUFFICES ASSUME NEW oe \in OO.edge
                  PROVE  oe \in NN \X NN
      OBVIOUS
    <2>1. PICK e \in EE : oe = <<e[2], e[1]>>
      OBVIOUS
    <2>2. PICK p \in DOMAIN upEdge : upEdge[p] = e /\ e # NotAnEdge
      OBVIOUS
    <2>3. e \in Edges /\ e \in Procs \X Procs
      BY <2>2, EdgeFacts
    <2>4. e[1] \in NN /\ e[2] \in NN
      BY <2>1
    <2>. QED  BY <2>1, <2>4
  <1>2. OO.node = NN
    OBVIOUS
  <1>3. \A oe \in OO.edge : oe[1] # Leader
    \* OO.edge entries are <<e[2], e[1]>> for e \in EE.  e[2] = p (some
    \* non-leader process from DOMAIN upEdge).
    <2>. SUFFICES ASSUME NEW oe \in OO.edge
                  PROVE  oe[1] # Leader
      OBVIOUS
    <2>1. PICK e \in EE : oe = <<e[2], e[1]>>
      OBVIOUS
    <2>2. PICK p \in DOMAIN upEdge : upEdge[p] = e /\ e # NotAnEdge
      OBVIOUS
    <2>3. p \in Procs \ {Leader}
      OBVIOUS
    <2>4. InTree(p)
      BY <2>2
    <2>5. e[2] = p
      BY <2>2, <2>3, <2>4
    <2>6. oe[1] = e[2]
      BY <2>1
    <2>. QED  BY <2>3, <2>5, <2>6
  <1>4. \A oe \in OO.edge :
          \A of \in OO.edge : (oe[1] = of[1]) => (oe = of)
    \* If two OO-edges share a source (= original target = the child),
    \* then they correspond to the same upEdge[p] for the same p.
    <2>. SUFFICES ASSUME NEW oe \in OO.edge, NEW of \in OO.edge,
                         oe[1] = of[1]
                  PROVE  oe = of
      OBVIOUS
    <2>1. PICK e1 \in EE : oe = <<e1[2], e1[1]>>
      OBVIOUS
    <2>2. PICK e2 \in EE : of = <<e2[2], e2[1]>>
      OBVIOUS
    <2>3. PICK p1 \in DOMAIN upEdge : upEdge[p1] = e1 /\ e1 # NotAnEdge
      OBVIOUS
    <2>4. PICK p2 \in DOMAIN upEdge : upEdge[p2] = e2 /\ e2 # NotAnEdge
      OBVIOUS
    <2>5. p1 \in Procs \ {Leader} /\ p2 \in Procs \ {Leader}
      OBVIOUS
    <2>6. InTree(p1) /\ InTree(p2)
      BY <2>3, <2>4
    <2>7. e1[2] = p1 /\ e2[2] = p2
      BY <2>5, <2>6, <2>3, <2>4
    <2>8. oe[1] = p1 /\ of[1] = p2
      BY <2>1, <2>2, <2>7
    <2>9. p1 = p2
      BY <2>8
    <2>10. e1 = e2
      BY <2>3, <2>4, <2>9
    <2>. QED  BY <2>1, <2>2, <2>10
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4

(***************************************************************************)
(* The connectivity part of IsTreeWithRoot says every node has a path to   *)
(* the root.  We construct that path by iterating upEdge.  This requires   *)
(* SimplePath / Cardinality reasoning which is delicate; we leave the      *)
(* concrete path-construction OMITTED and discharge the rest of            *)
(* IsTreeWithRoot from TreeStructure.                                      *)
(*                                                                         *)
(* AreConnectedIn(n, Leader, OO) follows from the chain                    *)
(*   n -> upEdge[n][1] -> upEdge[upEdge[n][1]][1] -> ... -> Leader         *)
(* which terminates by NoCycle + Procs finite.                             *)
(***************************************************************************)
LEMMA AreConnectedToLeader ==
  ASSUME Inv1, Inv2, NoCycle, NEW n \in OO.node
  PROVE  G!AreConnectedIn(n, Leader, OO)
  OMITTED

LEMMA TreeIsTree ==
  ASSUME Inv1, Inv2, NoCycle, OO.edge # {}
  PROVE  G!IsTreeWithRoot(OO, Leader)
  <1>. USE DEF G!IsTreeWithRoot, G!IsDirectedGraph, OO, G!Transpose
  <1>1. OO = [node |-> OO.node, edge |-> OO.edge]
    BY DEF OO, G!Transpose
  <1>2. OO.edge \subseteq OO.node \X OO.node
    BY TreeStructure DEF OO, G!Transpose
  <1>3. \A e \in OO.edge : /\ e[1] # Leader
                           /\ \A f \in OO.edge :
                                (e[1] = f[1]) => (e = f)
    BY TreeStructure
  <1>4. \A nn \in OO.node : G!AreConnectedIn(nn, Leader, OO)
    BY AreConnectedToLeader
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4

(***************************************************************************)
(* The body of TreeWithRoot (under []), with module-level OO/NN/EE.        *)
(***************************************************************************)
TreeBody ==
  /\ OO.edge # {} => G!IsTreeWithRoot(OO, Leader)
  /\ \A n \in OO.node: ~neutral(n)

(***************************************************************************)
(* The structural pieces above (TreeNodesNonNeutral / TreeStructure /      *)
(* TreeIsTree) discharge most of TreeWithRoot.  The QED below would close *)
(* the proof; it requires:                                                 *)
(*  (a) AreConnectedToLeader (OMITTED above) -- the SimplePath / Cardinal- *)
(*      ity / SeqOf reasoning to construct a path from any node to the     *)
(*      leader by iterating upEdge.                                        *)
(*  (b) Bridging the syntactic gap between TreeWithRoot's `LET ... IN []`  *)
(*      shape and our `[]TreeBody` form.  The two are semantically equal   *)
(*      because LET is just substitution, but TLAPS' temporal backend      *)
(*      currently does not unify them.                                     *)
(***************************************************************************)
LEMMA Inv2GivesTreeBody == Inv1 /\ Inv2 /\ NoCycle => TreeBody
  <1>. SUFFICES ASSUME Inv1, Inv2, NoCycle  PROVE TreeBody
    OBVIOUS
  <1>1. OO.edge # {} => G!IsTreeWithRoot(OO, Leader)
    BY TreeIsTree
  <1>2. \A n \in OO.node : ~ neutral(n)
    <2>1. OO.node = NN
      BY TreeStructure
    <2>. QED  BY <2>1, TreeNodesNonNeutral
  <1>. QED  BY <1>1, <1>2 DEF TreeBody

LEMMA SpecGivesAlwaysTreeBody == Spec => [] TreeBody
  <1>1. Spec => []Inv1
    BY Inv1Inductive
  <1>2. Spec => []Inv2
    BY Inv2Inductive
  <1>3. Spec => []NoCycle
    BY NoCycleInductive
  <1>. QED  BY <1>1, <1>2, <1>3, Inv2GivesTreeBody, PTL

THEOREM Thm_TreeWithRoot == Spec => TreeWithRoot
OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(* Theorem 4: Spec => DT2  (liveness)                                      *)
(*                                                                         *)
(* Liveness:  Terminated ~> neutral(Leader).                               *)
(*                                                                         *)
(* Once the computation has globally terminated, the WF_vars(Next)         *)
(* fairness assumption guarantees progress on each remaining               *)
(* RcvMsg/SendAck/RcvAck step until all counters drain to 0 and the       *)
(* leader becomes neutral.  A multiset/well-founded measure on             *)
(* (msgs, rcvdUnacked, acks, sentUnacked) is needed; left as future work.  *)
(***************************************************************************)
THEOREM Thm_DT2 == Spec => DT2
OMITTED

=============================================================================
