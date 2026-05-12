--------------------------- MODULE SpanTree_proof -----------------------------
(***************************************************************************)
(* TLAPS proof of  Spec => []TypeOK.                                       *)
(***************************************************************************)
EXTENDS SpanTree, TLAPS

(***************************************************************************)
(* Restate the spec's unnamed ASSUME for proof use.                        *)
(***************************************************************************)
ASSUME ConstantsAssumption ==
  /\ Root \in Nodes
  /\ \A e \in Edges : (e \subseteq Nodes) /\ (Cardinality(e) = 2)
  /\ MaxCardinality \in Nat
  /\ MaxCardinality >= Cardinality(Nodes)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY ConstantsAssumption DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>. SUFFICES ASSUME TypeOK, [Next]_vars  PROVE TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. CASE Next
    <3>. PICK n \in Nodes :
            \E m \in Nbrs(n) :
               /\ dist[m] < 1 + dist[n]
               /\ \E d \in (dist[m]+1) .. (dist[n] - 1) :
                     /\ dist' = [dist EXCEPT ![n] = d]
                     /\ mom'  = [mom  EXCEPT ![n] = m]
      BY <2>1 DEF Next
    <3>. PICK m \in Nbrs(n) :
            /\ dist[m] < 1 + dist[n]
            /\ \E d \in (dist[m]+1) .. (dist[n] - 1) :
                  /\ dist' = [dist EXCEPT ![n] = d]
                  /\ mom'  = [mom  EXCEPT ![n] = m]
      OBVIOUS
    <3>1. m \in Nodes
      BY DEF Nbrs
    <3>2. PICK d \in (dist[m]+1) .. (dist[n] - 1) :
              /\ dist' = [dist EXCEPT ![n] = d]
              /\ mom'  = [mom  EXCEPT ![n] = m]
      OBVIOUS
    <3>3. dist[m] \in Nat /\ dist[n] \in Nat
      BY <3>1
    <3>4. d \in Nat
      BY <3>2, <3>3
    <3>5. dist' = [dist EXCEPT ![n] = d]
      BY <3>2
    <3>6. mom' = [mom EXCEPT ![n] = m]
      BY <3>2
    <3>7. dist' \in [Nodes -> Nat]
      BY <3>4, <3>5
    <3>8. mom' \in [Nodes -> Nodes]
      BY <3>1, <3>6
    <3>. QED  BY <3>7, <3>8
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF vars
  <2>. QED  BY <2>1, <2>2
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
============================================================================
