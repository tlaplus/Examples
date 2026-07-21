--------------------------- MODULE EWD687a_proof ---------------------------
(***************************************************************************)
(* Proofs of the theorems stated in EWD687a.tla.                           *)
(***************************************************************************)
EXTENDS EWD687a, NaturalsInduction, FiniteSetTheorems, GraphTheorems, TLAPS

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
Inv1 == TypeOK /\ CountersConsistent

THEOREM Invariant1 == Spec => []Inv1 
<1>1. Init => Inv1 
  BY DEF Init, Inv1, TypeOK, CountersConsistent, NotAnEdge
<1>2. Inv1 /\ [Next]_vars => Inv1'
  <2> SUFFICES ASSUME Inv1, [Next]_vars
               PROVE  Inv1'
    OBVIOUS
  <2>. USE DEF Inv1, TypeOK, CountersConsistent
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
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM TypeCorrect == Spec => []TypeOK
BY Invariant1, PTL DEF Inv1

THEOREM Thm_CountersConsistent == Spec => CountersConsistent
BY Invariant1, PTL DEF CountersConsistent, Inv1

-----------------------------------------------------------------------------
(***************************************************************************)
(* In preparation of the main correctness theorem expressed by DT1Inv, we  *)
(* prove a strengthening of invariant TreeWithRoot.                        *)
(***************************************************************************)
TreeInv ==
    /\ TreeWithRoot 
    /\ \A p \in Procs \ {Leader} :
          /\ upEdge[p] = NotAnEdge => neutral(p)
          /\ upEdge[p] # NotAnEdge => 
               /\ upEdge[p] \in InEdges(p)
               /\ rcvdUnacked[upEdge[p]] # 0

LEMMA NotAnEdgeNoEdge == NotAnEdge \notin Edges
BY EdgeFacts DEF NotAnEdge 

THEOREM TreeInvariant == Spec => []TreeInv 
<1>. DEFINE E == {upEdge[p] : p \in DOMAIN upEdge} \ {NotAnEdge}
            N == {e[2] : e \in E} \cup {Leader}
            T == [node |-> N, edge |-> E]
            O == Transpose(T)
\* introductory steps for removing the LET in the definition of TreeWithRoot:
\* this allows us to hide the definitions of E, N, and O and reduce the size
\* of the formulas given to the backends
<1>1. TreeWithRoot <=> /\ IsTreeWithRoot(O, Leader)
                       /\ \A n \in N \ {Leader} : ~ neutral(n)
  BY DEF TreeWithRoot, Transpose 
<1>2. TreeWithRoot' <=> /\ IsTreeWithRoot(O', Leader)
                        /\ \A n \in N' \ {Leader} : ~ neutral(n)'
  BY DEF TreeWithRoot, Transpose
<1>3. Init => TreeInv 
  <2>. SUFFICES ASSUME Init PROVE TreeWithRoot
    BY DEF Init, TreeInv, neutral, InEdges, OutEdges
  <2>. /\ N = {Leader}
       /\ O = [edge |-> {}, node |-> N]
    BY Zenon DEF Init, Transpose
  <2>. HIDE DEF O, N
  <2>. QED  BY <1>1, SingletonIsTreeWithRoot
<1>4. Inv1 /\ Inv1' /\ TreeInv /\ [Next]_vars => TreeInv'
  <2>. SUFFICES ASSUME TypeOK, TypeOK', CountersConsistent, TreeInv, [Next]_vars 
                PROVE TreeInv'
    BY DEF Inv1
  <2>. USE DEF TypeOK
  \* Because we have a tree, both ends of each edge are nodes
  <2>1. ASSUME NEW e \in E  PROVE e[1] \in N 
    <3>. E \subseteq Edges
      OBVIOUS 
    <3>. HIDE DEF E, N, O
    <3>1. IsTreeWithRoot(O, Leader)
      BY <1>1 DEF TreeInv 
    <3>2. e[2] \in O.node
      BY DEF Transpose, O, N 
    <3>3. PICK p \in Path(O) : p[1] = e[2] /\ p[Len(p)] = Leader 
      BY <3>1, <3>2 DEF IsTreeWithRoot, AreConnectedIn
    <3>. p \in Seq(O.node) \ { <<>> }
      BY DEF Path
    <3>4. e[2] # Leader 
      BY EdgeFacts DEF InEdges
    <3>5. 1 \in 1 .. Len(p)-1
      BY <3>3, <3>4
    <3>6. <<p[1], p[2]>> \in O.edge 
      BY <3>5 DEF Path 
    <3>7. <<e[2], e[1]>> \in O.edge 
      BY EdgeFacts DEF O, Transpose 
    <3>8. <<p[1], p[2]>> = <<e[2], e[1]>> 
      BY <3>1, <3>3, <3>6, <3>7 DEF IsTreeWithRoot
    <3>9. e[1] \in O.node 
      BY <3>5, <3>8
    <3>. QED  BY <3>9 DEF O, Transpose 
  <2>2. IsDirectedGraph(T)
    BY EdgeFacts, <2>1 DEF IsDirectedGraph
  <2>3. /\ N \subseteq Procs
        /\ N' \subseteq Procs
    BY EdgeFacts
  <2>4. ASSUME NEW p \in Procs, SendMsg(p) PROVE TreeInv'
    <3>1. UNCHANGED <<O, N, upEdge, rcvdUnacked>>
      BY <2>4 DEF SendMsg
    <3>2. \A n \in Procs : neutral(n)' <=> neutral(n)
      BY <2>4 DEF SendMsg, neutral, InEdges, OutEdges 
    <3>. HIDE DEF O, N
    <3>. QED  BY <1>1, <1>2, <2>3, <3>1, <3>2 DEF TreeInv
  <2>5. ASSUME NEW p \in Procs, SendAck(p) PROVE TreeInv'
    <3>1. PICK e \in InEdges(p) : 
               /\ rcvdUnacked[e] > 0 
               /\ e = upEdge[p] => 
                    \/ rcvdUnacked[e] > 1
                    \/ /\ ~ active[p] 
                       /\ \A d \in InEdges(p) \ {e} : rcvdUnacked[d] = 0
                       /\ \A d \in OutEdges(p) : sentUnacked[d] = 0
               /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ - 1] 
               /\ acks' = [acks EXCEPT ![e] = @ + 1]
               /\ upEdge' = IF neutral(p)' THEN [upEdge EXCEPT ![p] = NotAnEdge]
                                           ELSE upEdge
               /\ UNCHANGED <<active, msgs, sentUnacked>>
      BY <2>5 DEF SendAck
    <3>. e \in Edges /\ p # Leader
      BY EdgeFacts DEF InEdges
    <3>2. ~ neutral(p)
      BY <3>1 DEF neutral, InEdges
    <3>3. \A q \in Procs \ {p} : neutral(q)' <=> neutral(q)
      BY <3>1 DEF neutral, InEdges, OutEdges
    <3>4. CASE neutral(p)'
      <4>1. ASSUME NEW q \in Procs \ {Leader}
            PROVE  /\ upEdge'[q] = NotAnEdge => neutral(q)'
                   /\ upEdge'[q] # NotAnEdge =>
                        /\ upEdge'[q] \in InEdges(q)
                        /\ rcvdUnacked'[upEdge'[q]] # 0
        <5>1. CASE q = p
          BY <3>1, <3>4, <5>1
        <5>2. CASE q # p 
          BY <3>1, <3>3, <5>2, NotAnEdgeNoEdge DEF TreeInv, InEdges
        <5>. QED  BY <5>1, <5>2
      <4>2. rcvdUnacked[e] = 1
        BY <3>1, <3>4 DEF neutral, InEdges 
      <4>3. e = upEdge[p] 
        <5>. SUFFICES ASSUME e # upEdge[p]  PROVE FALSE 
          OBVIOUS 
        <5>1. /\ upEdge[p] \in InEdges(p)
              /\ rcvdUnacked[upEdge[p]] # 0
          BY <3>2 DEF TreeInv 
        <5>2. PICK u \in InEdges(p) : u = upEdge[p]
          BY <5>1
        <5>3. rcvdUnacked'[u] # 0
          BY <3>1, <5>1, <5>2 DEF InEdges
        <5>. QED  BY <3>4, <5>3 DEF neutral 
      <4>4. ~ \E q \in Procs \ {Leader} : upEdge[q] \in OutEdges(p)
        <5>. SUFFICES ASSUME NEW q \in Procs \ {Leader}, upEdge[q] \in OutEdges(p)
                      PROVE  FALSE 
          OBVIOUS 
        <5>1. PICK u \in OutEdges(p) : u = upEdge[q]
          OBVIOUS 
        <5>2. /\ u \in InEdges(q)
              /\ rcvdUnacked[u] # 0
          BY NotAnEdgeNoEdge, <5>1 DEF TreeInv, OutEdges
        <5>3. sentUnacked[u] = rcvdUnacked[u] + acks[u] + msgs[u] 
          BY <5>2 DEF CountersConsistent, InEdges
        <5>4. sentUnacked[u] # 0
          BY <5>2, <5>3 DEF InEdges
        <5>. QED  BY <3>1, <3>4, <5>4 DEF neutral
      <4>5. /\ e \in E
            /\ e[2] = p
            /\ p \in N
        BY <3>2, <4>3 DEF TreeInv, InEdges
      <4>6. Successors(T, p) = {}
        BY EdgeFacts, <4>4 DEF Successors, OutEdges
      <4>7. E' = E \ {e}
        <5>1. E' \subseteq E 
          BY <3>1
        <5>2. ASSUME e \in E' PROVE FALSE 
          <6>1. PICK q \in Procs \ {Leader} : e = upEdge'[q] /\ e # NotAnEdge
            BY <5>2
          <6>2. q # p /\ e = upEdge[q]
            BY <3>1, <3>4, <6>1
          <6>3. e \in InEdges(q)
            BY <6>1, <6>2 DEF TreeInv 
          <6>. QED  BY <6>2, <6>3 DEF InEdges 
        <5>3. (E \ {e}) \subseteq E'
          BY <3>1, <4>3
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>8. N' = N \ {p}
        <5>1. N' \subseteq N 
          BY <3>1
        <5>2. p \notin N'
          BY <3>1, <3>4, <4>4 DEF OutEdges
        <5>3. (N \ {p}) \subseteq N' 
          BY <3>1
        <5>. QED  BY <5>1, <5>2, <5>3
      <4>. HIDE DEF N, E
      <4>9. IsTreeWithRoot(O', Leader)
        BY <1>1, EdgeFacts, RemoveLeafFromTransposedTree, <2>1, <2>2, <4>5, <4>6, <4>7, <4>8, SMTT(10)
           DEF TreeInv 
      <4>11. TreeWithRoot'
        BY <1>1, <1>2, <2>3, <3>3, <4>9, <4>8, Zenon DEF TreeInv
      <4>. QED  BY <4>1, <4>11 DEF TreeInv
    <3>5. CASE ~ neutral(p)'
      <4>1. UNCHANGED <<N, O, upEdge>> 
        BY <3>1, <3>5
      <4>2. ASSUME NEW q \in Procs \ {Leader}, upEdge[q] # NotAnEdge 
            PROVE  (rcvdUnacked[upEdge[q]] = 0) <=> (rcvdUnacked'[upEdge[q]] = 0)
        <5>1. CASE q = p
          BY <3>1, <3>5, <4>2, <5>1 DEF neutral, InEdges, OutEdges
        <5>2. CASE q # p
          BY <3>1, <4>2, <5>2 DEF TreeInv, InEdges
        <5>. QED  BY <5>1, <5>2
      <4>. HIDE DEF N, O 
      <4>. QED  BY <1>1, <1>2, <2>3, <3>2, <3>3, <3>5, <4>1, <4>2 DEF TreeInv 
    <3>. QED  BY <3>4, <3>5
  <2>6. ASSUME NEW p \in Procs, RcvMsg(p) PROVE TreeInv'
    <3>1. PICK e \in InEdges(p) :
               /\ msgs[e] > 0  
               /\ msgs' = [msgs EXCEPT ![e] = @ - 1]  
               /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ + 1]
               /\ active' = [active EXCEPT ![p] = TRUE]
               /\ upEdge' = IF neutral(p) THEN [upEdge EXCEPT ![p] = e]
                                          ELSE upEdge
               /\ UNCHANGED <<acks, sentUnacked>>
      BY <2>6 DEF RcvMsg 
    <3>. e \in Edges /\ p # Leader 
      BY EdgeFacts DEF InEdges
    <3>2. ~ neutral(p)'
      BY <3>1 DEF neutral
    <3>3. \A q \in Procs \ {p} : neutral(q)' <=> neutral(q)
      BY <3>1 DEF neutral, InEdges
    <3>4. CASE neutral(p) 
      <4>1. ASSUME NEW q \in Procs \ {Leader}
            PROVE  upEdge'[q] = NotAnEdge => neutral(q)'
        BY NotAnEdgeNoEdge, <3>1, <3>3, <3>4 DEF TreeInv 
      <4>2. ASSUME NEW q \in Procs \ {Leader}, upEdge'[q] # NotAnEdge 
            PROVE  /\ upEdge'[q] \in InEdges(q)
                   /\ rcvdUnacked'[upEdge'[q]] # 0
        BY <3>1, <3>4, <4>2 DEF TreeInv, InEdges 
      <4>3. p \notin N 
        BY <1>1, <3>4 DEF TreeInv 
      <4>4. e[1] \in N 
        <5>. e[1] \in Procs 
          BY EdgeFacts
        <5>1. e \in OutEdges(e[1]) /\ sentUnacked[e] # 0
          BY <3>1 DEF CountersConsistent, OutEdges
        <5>2. ~ neutral(e[1])
          BY <5>1 DEF neutral 
        <5>. QED  BY <5>2 DEF TreeInv 
      <4>5. E' = E \cup {e}
        BY NotAnEdgeNoEdge, <3>1, <3>4, <4>3
      <4>6. N' = N \cup {p}
        BY <4>5 DEF InEdges
      <4>. HIDE DEF N, E
      <4>7. IsTreeWithRoot(O', Leader)
        BY EdgeFacts, <1>1, AddLeafToTransposedTree, <2>2, <4>3, <4>4, <4>5, <4>6, SMTT(10)
           DEF TreeInv, InEdges
      <4>8. \A n \in N' \ {Leader} : ~ neutral(n)'
        BY <1>1, <2>3, <3>2, <3>3, <4>6 DEF TreeInv 
      <4>. QED  BY <1>2, <4>1, <4>2, <4>7, <4>8, Zenon DEF TreeInv 
    <3>5. CASE ~ neutral(p)
      <4>1. UNCHANGED <<upEdge, N, O>> 
        BY <3>1, <3>5
      <4>. HIDE DEF O
      <4>2. TreeWithRoot'
        BY <1>1, <1>2, <2>3, <3>2, <3>3, <3>5, <4>1, Zenon DEF TreeInv 
      <4>. QED  BY <4>2, <3>1, <3>2, <3>3, <3>5, <4>1 DEF TreeInv 
    <3>. QED  BY <3>4, <3>5
  <2>7. ASSUME NEW p \in Procs, RcvAck(p) PROVE TreeInv'
    <3>1. UNCHANGED <<O, N, upEdge, rcvdUnacked>> 
      BY <2>7 DEF RcvAck
    <3>2. ASSUME NEW q \in Procs \ {Leader}
          PROVE  neutral(q)' <=> neutral(q)
      <4>1. CASE q = p 
        <5>1. ~ neutral(p)
          BY <2>7 DEF RcvAck, neutral, CountersConsistent, OutEdges 
        <5>2. /\ upEdge[p] \in InEdges(p)
              /\ rcvdUnacked[upEdge[p]] # 0
          BY <4>1, <5>1 DEF TreeInv 
        <5>. QED  BY <3>1, <4>1, <5>1, <5>2 DEF neutral 
      <4>2. CASE q # p 
        BY <2>7, <4>2 DEF RcvAck, neutral, InEdges, OutEdges
      <4>. QED  BY <4>1, <4>2
    <3>. HIDE DEF N, O
    <3>. QED  BY <1>1, <1>2, <2>3, <3>1, <3>2 DEF TreeInv 
  <2>8. ASSUME NEW p \in Procs, Idle(p) PROVE TreeInv'
    <3>1. UNCHANGED <<N, O, upEdge, rcvdUnacked>> 
      BY <2>8 DEF Idle 
    <3>2. ASSUME NEW q \in Procs \ {Leader}
          PROVE  neutral(q)' <=> neutral(q)
      <4>1. CASE q = p 
        <5>1. ~ neutral(p)
          BY <2>8 DEF Idle, neutral 
        <5>2. /\ upEdge[p] \in InEdges(p)
              /\ rcvdUnacked[upEdge[p]] # 0
          BY <4>1, <5>1 DEF TreeInv 
        <5>. QED  BY <3>1, <4>1, <5>1, <5>2 DEF neutral 
      <4>2. CASE q # p 
        BY <2>8, <4>2 DEF Idle, neutral, InEdges, OutEdges
      <4>. QED  BY <4>1, <4>2
    <3>. QED  BY <1>1, <1>2, <2>3, <3>1, <3>2 DEF TreeInv 
  <2>9. CASE UNCHANGED vars
    BY <2>9 DEF vars, TreeInv, TreeWithRoot, neutral, InEdges, OutEdges
  <2>. QED  BY <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next
<1>. QED  BY <1>3, <1>4, Invariant1, PTL DEF Spec 

-----------------------------------------------------------------------------
(***************************************************************************)
(* We can now prove the main safety property of the algorithm, expressed   *)
(* as DT1Inv, as a consequence of the preceding invariants.                *)
(***************************************************************************)
THEOREM Safety == Spec => []DT1Inv 
<1>1. Inv1 /\ TreeInv => DT1Inv 
  <2>. DEFINE S == {p \in Procs \ {Leader} : ~ neutral(p)}
  <2>. SUFFICES ASSUME TypeOK, CountersConsistent, TreeInv, neutral(Leader), S # {} 
                 PROVE  FALSE 
    BY DEF Inv1, DT1Inv 
  <2>. USE DEF TypeOK
  <2>. DEFINE E == {upEdge[p] : p \in DOMAIN upEdge} \ {NotAnEdge}
              N == {e[2] : e \in E} \cup {Leader}
              T == [node |-> N, edge |-> E]
              O == Transpose(T)
  <2>1. IsTreeWithRoot(O, Leader)
    BY DEF TreeInv, TreeWithRoot
  <2>2. O.node = N 
    BY DEF Transpose
  <2>3. S \subseteq N 
    BY DEF TreeInv 
  <2>4. PICK q \in S : \A e \in O.edge : e[1] = q => e[2] \notin S 
    <3>. HIDE DEF N, O, S
    <3>. QED  BY TreeAcyclic, <2>1, <2>2, <2>3, Zenon
  <2>. DEFINE e == upEdge[q]  parent == e[1]
  <2>5. /\ e # NotAnEdge
        /\ e \in InEdges(q)
        /\ rcvdUnacked[e] # 0
    BY DEF TreeInv 
  <2>6. /\ e \in OutEdges(parent)
        /\ e = <<parent, q>>
    BY EdgeFacts, <2>5 DEF InEdges, OutEdges
  <2>7. sentUnacked[e] # 0
    BY <2>5 DEF CountersConsistent, InEdges
  <2>8. ~ neutral(parent)
    BY <2>6, <2>7 DEF neutral
  <2>9. parent \in S 
    BY EdgeFacts, <2>5, <2>8
  <2>10. <<q, parent>> \in O.edge 
    BY <2>5, <2>6 DEF Transpose
  <2>. HIDE DEF O, S
  <2>. QED  BY <2>4, <2>9, <2>10
<1>. QED  BY <1>1, Invariant1, TreeInvariant, PTL

-----------------------------------------------------------------------------
(***************************************************************************)
(* The proof of the liveness property DT2 is left for future work.         *)
(***************************************************************************)

=============================================================================
