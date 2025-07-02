---------------------------- MODULE EWD840_proof ----------------------------
(***************************************************************************)
(* This module contains the proof of the safety properties of Dijkstra's   *)
(* termination detection algorithm. Checking the proof requires TLAPS to   *)
(* be installed.                                                           *)
(***************************************************************************)
EXTENDS EWD840, NaturalsInduction, TLAPS
USE NAssumption

(***************************************************************************)
(* The algorithm is type-correct: TypeOK is an inductive invariant.        *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, Color
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK, Node, Color
  <2>1. CASE InitiateProbe
    BY <2>1 DEF InitiateProbe
  <2>2. ASSUME NEW i \in Node \ {0},
               PassToken(i)
        PROVE  TypeOK'
    BY <2>2 DEF PassToken
  <2>3. ASSUME NEW i \in Node,
               SendMsg(i)
        PROVE  TypeOK'
    BY <2>3 DEF SendMsg
  <2>4. ASSUME NEW i \in Node,
               Deactivate(i)
        PROVE  TypeOK'
    BY <2>4 DEF Deactivate
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Environment, Next, System
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Prove the main soundness property of the algorithm by (1) proving that  *)
(* Inv is an inductive invariant and (2) that it implies correctness.      *)
(***************************************************************************)
THEOREM Invariant == Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv, Node
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  BY DEF TypeOK, Inv, Next, vars, Node, Color,
         System, Environment, InitiateProbe, PassToken, SendMsg, Deactivate
<1>. QED
  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM Safety == Spec => []TerminationDetection
<1>. Inv => TerminationDetection
  BY DEF Inv, TerminationDetection, terminationDetected, terminated, Node
<1>. QED
  BY Invariant, TypeCorrect, PTL

(***************************************************************************)
(* The above proof shows that Dijkstra's invariant implies the predicate   *)
(* TerminationDetection. If you find that one-line proof too obscure, here *)
(* is a more detailed, hierarchical proof of that same implication.        *)
(***************************************************************************)
LEMMA Inv => TerminationDetection
<1>1. SUFFICES ASSUME tpos = 0, tcolor = "white", 
                      color[0] = "white", ~ active[0],
                      Inv
               PROVE  \A i \in Node : ~ active[i]
  BY <1>1 DEF TerminationDetection, terminationDetected, terminated
<1>2. ~ Inv!P2  BY tcolor = "white" DEF Inv
<1>3. ~ Inv!P1  BY <1>1 DEF Inv
<1>. QED
  <2>1. Inv!P0  BY Inv, <1>2, <1>3 DEF Inv
  <2>.  TAKE i \in Node
  <2>3. CASE i = 0  BY <2>1, <1>1, <2>3
  <2>4. CASE i \in 1 .. N-1
    <3>1. tpos < i  BY tpos=0, <2>4, NAssumption
    <3>2. i < N  BY <2>4
    <3>. QED  BY <3>1, <3>2, <2>1
  <2>. QED  BY <2>3, <2>4 DEF Node

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness of the algorithm.                                              *)
(***************************************************************************)

(***************************************************************************)
(* The proof of liveness relies on the fairness condition assumed for the  *)
(* algorithm, which in turn is defined in terms of enabledness. It is      *)
(* usually a good idea to reduce that enabledness condition to a standard  *)
(* state predicate, and the following lemma does just that.                *)
(***************************************************************************)
LEMMA EnabledSystem ==
    ASSUME TypeOK 
    PROVE  (ENABLED <<System>>_vars) <=> 
              \/ tpos = 0 /\ (tcolor = "black" \/ color[0] = "black")
              \/ tpos \in Node \ {0} /\ (~active[tpos] \/ tcolor = "black" \/ color[tpos] = "black")
<1>1. <<System>>_vars <=> System
  <2>1. InitiateProbe => <<InitiateProbe>>_vars
    BY DEF TypeOK, InitiateProbe, vars
  <2>2. ASSUME NEW i \in Node \ {0}
        PROVE  PassToken(i) => <<PassToken(i)>>_vars
    BY <2>2 DEF Node, PassToken, vars
  <2>. QED  BY <2>1, <2>2 DEF System
<1>2. (ENABLED <<System>>_vars) <=> (ENABLED System)
  BY <1>1, ENABLEDaxioms
<1>. QED BY <1>2, ExpandENABLED DEF System, InitiateProbe, PassToken, vars

(***************************************************************************)
(* We need to prove that once the system has globally terminated, the      *)
(* condition for detecting termination must eventually become true. As is  *)
(* often the case with proving liveness, it is convenient to carry out     *)
(* this proof by contradiction, so we also assume that termination is      *)
(* never detected. The system may require three rounds:                    *)
(* 1. The first round brings the token back to node 0.                     *)
(* 2. The second round cleans all nodes.                                   *)
(* 3. The third round brings back a clean token.                           *)
(***************************************************************************)

(***************************************************************************)
(* Specification used for the liveness proof: we ignore the initial state  *)
(* predicate but include the invariants of the algorithm. We also assume,  *)
(* for the sake of contradiction, that termination is never detected.      *)
(***************************************************************************)
TSpec ==
    /\ []TypeOK
    /\ []Inv
    /\ []~terminationDetected
    /\ [][Next]_vars
    /\ WF_vars(System)

allWhite == \A n \in Node : color[n] = "white"

(***************************************************************************)
(* The following three lemmas represent the idea of the system needing up  *)
(* to three complete rounds of the token for detecting termination. Their  *)
(* proofs rely on induction on the initial position of the token, and they *)
(* are essentially obtained by copy-and-paste.                             *)
(***************************************************************************)
LEMMA Round1 ==
    TSpec => (terminated ~> (terminated /\ tpos = 0))
<1>. DEFINE P(n) == terminated /\ n \in Node /\ tpos = n
            Q == P(0)
            R(n) == TSpec => [](P(n) => <>Q)
<1>1. \A n \in Nat : R(n)
  <2>1. R(0)
    BY PTL
  <2>2. ASSUME NEW n \in Nat PROVE R(n) => R(n+1)
    <3>. DEFINE Pn == P(n)  Pn1 == P(n+1)
    <3>. USE DEF TypeOK, Node, Color, terminated 
    <3>1. TypeOK /\ Pn1 /\ [Next]_vars => Pn1' \/ Pn'
      BY DEF Next, vars, System, Environment, InitiateProbe, PassToken, Deactivate, SendMsg
    <3>2. TypeOK /\ Pn1 /\ <<System>>_vars => Pn'
      BY DEF System, vars, InitiateProbe, PassToken
    <3>3. TypeOK /\ Pn1 => ENABLED <<System>>_vars
      BY EnabledSystem
    <3>. QED  BY <3>1, <3>2, <3>3, PTL DEF TSpec
  <2>. HIDE DEF R 
  <2>. QED  BY <2>1, <2>2, NatInduction, Isa
<1>2. TSpec => []((\E n \in Nat : P(n)) => <>Q)
  <2>. HIDE DEF P,Q
  <2>1. TSpec => [](\A n \in Nat : P(n) => <>Q)
    BY <1>1
  <2>2. (\A n \in Nat : P(n) => <>Q) => ((\E n \in Nat : P(n)) => <>Q)
    OBVIOUS
  <2>. QED  BY <2>1, <2>2, PTL
<1>3. TypeOK => (terminated => \E n \in Nat : P(n))
  BY DEF TypeOK, terminated, Node
<1>. QED  BY <1>2, <1>3, PTL DEF TSpec

LEMMA Round2 == TSpec => (terminated /\ tpos = 0
                            ~> terminated /\ tpos = 0 /\ allWhite)
<1>. DEFINE P(n) == /\ terminated /\ n \in Node /\ tpos = n
                    /\ color[0] = "white"
                    /\ \A i \in n+1 .. N-1 : color[i] = "white"
            Q == P(0)
            R(n) == TSpec => [](P(n) => <>Q)
<1>1. \A n \in Nat : R(n)
  <2>1. R(0)
    BY PTL
  <2>2. ASSUME NEW n \in Nat PROVE R(n) => R(n+1)
    <3>. USE DEF TypeOK, Node, terminated
    <3>1. TypeOK /\ P(n+1) /\ [Next]_vars => P(n+1)' \/ P(n)'
      BY DEF Next, vars, System, Environment, InitiateProbe, 
             PassToken, Deactivate, SendMsg
    <3>2. TypeOK /\ P(n+1) /\ <<System>>_vars => P(n)'
      BY DEF System, InitiateProbe, PassToken
    <3>3. TypeOK /\ P(n+1) => ENABLED <<System>>_vars
      BY EnabledSystem
    <3>. QED  BY <3>1, <3>2, <3>3, PTL DEF TSpec
  <2>. HIDE DEF R
  <2>. QED  BY <2>1, <2>2, NatInduction, Isa
<1>2. TSpec => []((\E n \in Nat : P(n)) => <>Q)
  <2>. HIDE DEF P,Q
  <2>1. TSpec => [](\A n \in Nat : P(n) => <>Q)
    BY <1>1
  <2>2. (\A n \in Nat : P(n) => <>Q) => ((\E n \in Nat : P(n)) => <>Q)
    OBVIOUS
  <2>. QED  BY <2>1, <2>2, PTL
<1>3. TSpec => (terminated /\ tpos = 0 ~> \E n \in Nat : P(n))
  <2>. DEFINE S == terminated /\ tpos = 0
              T == P(N-1)
  <2>1. TypeOK /\ S /\ [Next]_vars => S' \/ T'
    BY DEF TypeOK, Next, vars, System, Environment, InitiateProbe, PassToken, 
           Deactivate, SendMsg, terminated, Node
  <2>2. TypeOK /\ S /\ <<System>>_vars => T'
    BY DEF TypeOK, System, InitiateProbe, PassToken, terminated, Node
  <2>3. TypeOK /\ ~terminationDetected /\ S => ENABLED <<System>>_vars
    BY EnabledSystem DEF TypeOK, terminationDetected, terminated, Color
  <2>4. T => \E n \in Nat : P(n)
    OBVIOUS
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, PTL DEF TSpec
<1>4. Q => terminated /\ tpos = 0 /\ allWhite
  BY DEF Node, allWhite
<1>. QED  BY <1>2, <1>3, <1>4, PTL

LEMMA Round3 == TSpec => (terminated /\ tpos = 0 /\ allWhite
                            ~> terminated /\ tpos = 0 /\ allWhite /\ tcolor = "white")
<1>. DEFINE P(n) == /\ terminated /\ n \in Node /\ tpos = n
                    /\ allWhite /\ tcolor = "white"
            Q == P(0)
            R(n) == TSpec => [](P(n) => <>Q)
<1>1. \A n \in Nat : R(n)
  <2>1. R(0)
    BY PTL
  <2>2. ASSUME NEW n \in Nat PROVE R(n) => R(n+1)
    <3>. USE DEF TypeOK, Node, terminated, allWhite
    <3>1. TypeOK /\ P(n+1) /\ [Next]_vars => P(n+1)' \/ P(n)'
      BY DEF Next, vars, System, Environment, InitiateProbe, 
             PassToken, Deactivate, SendMsg
    <3>2. TypeOK /\ P(n+1) /\ <<System>>_vars => P(n)'
      BY DEF System, InitiateProbe, PassToken
    <3>3. TypeOK /\ P(n+1) => ENABLED <<System>>_vars
      BY EnabledSystem
    <3>. QED  BY <3>1, <3>2, <3>3, PTL DEF TSpec
  <2>. HIDE DEF R
  <2>. QED  BY <2>1, <2>2, NatInduction, Isa
<1>2. TSpec => []((\E n \in Nat : P(n)) => <>Q)
  <2>. HIDE DEF P,Q
  <2>1. TSpec => [](\A n \in Nat : P(n) => <>Q)
    BY <1>1
  <2>2. (\A n \in Nat : P(n) => <>Q) => ((\E n \in Nat : P(n)) => <>Q)
    OBVIOUS
  <2>. QED  BY <2>1, <2>2, PTL
<1>3. TSpec => (terminated /\ tpos = 0 /\ allWhite ~> \E n \in Nat : P(n))
  <2>. DEFINE S == terminated /\ tpos = 0 /\ allWhite
              T == P(N-1)
  <2>. USE DEF TypeOK, Node, terminated, allWhite
  <2>1. TypeOK /\ S /\ [Next]_vars => S' \/ T'
    BY DEF Next, vars, System, Environment, InitiateProbe, PassToken, 
           Deactivate, SendMsg
  <2>2. TypeOK /\ S /\ <<System>>_vars => T'
    BY DEF System, InitiateProbe, PassToken
  <2>3. TypeOK /\ ~terminationDetected /\ S => ENABLED <<System>>_vars
    BY EnabledSystem DEF terminationDetected, Color
  <2>4. T => \E n \in Nat : P(n)
    OBVIOUS
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, PTL DEF TSpec
<1>4. Q => terminated /\ tpos = 0 /\ allWhite /\ tcolor = "white"
  BY DEF Node, allWhite
<1>. QED  BY <1>2, <1>3, <1>4, PTL

(***************************************************************************)
(* Liveness is a simple consequence of the above lemmas.                   *)
(***************************************************************************)
THEOREM Live == []TypeOK /\ []Inv /\ [][Next]_vars /\ WF_vars(System) => Liveness
<1>. terminated /\ tpos = 0 /\ allWhite /\ tcolor = "white" => terminationDetected
  BY DEF terminated, allWhite, terminationDetected, Node
<1>. QED
  BY Round1, Round2, Round3, PTL DEF TSpec, Liveness

COROLLARY SpecLive == Spec => Liveness
BY Live, TypeCorrect, Invariant, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* The algorithm implements the high-level specification of termination    *)
(* detection in a ring with synchronous communication between nodes.       *)
(* Note that the parameters of the module SyncTerminationDetection are     *)
(* instantiated by the symbols of the same name in the present module.     *)
(***************************************************************************)
THEOREM Spec => TD!Spec
<1>. USE DEF Node, TD!Node
<1>1. Init => TD!Init
  BY DEF Init, TD!Init, terminationDetected
<1>2. TypeOK /\ Inv /\ [Next]_vars => [TD!Next]_TD!vars
  <2>. SUFFICES ASSUME TypeOK, Inv, Next PROVE [TD!Next]_TD!vars
    BY DEF vars, TD!vars, terminationDetected
  <2>. USE DEF TypeOK, Inv, Node, terminationDetected
  <2>1. CASE InitiateProbe
    BY <2>1 DEF InitiateProbe, TD!Next, TD!vars, TD!DetectTermination, TD!terminated
  <2>2. ASSUME NEW i \in Node \ {0}, PassToken(i) PROVE [TD!Next]_TD!vars
    BY <2>2 DEF PassToken, TD!Next, TD!vars, TD!DetectTermination, TD!terminated
  <2>3. ASSUME NEW i \in Node, SendMsg(i) PROVE [TD!Next]_TD!vars
    BY <2>3 DEF SendMsg, TD!Next, TD!Wakeup
  <2>4. ASSUME NEW i \in Node, Deactivate(i) PROVE [TD!Next]_TD!vars
    BY <2>4 DEF Deactivate, TD!Next, TD!Terminate, TD!terminated
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4 DEF Next, System, Environment
<1>3. []TypeOK /\ []Inv /\ [][Next]_vars /\ WF_vars(System)
      => WF_TD!vars(TD!DetectTermination)
  <2>. SUFFICES /\ []TypeOK /\ []Inv /\ [][Next]_vars /\ WF_vars(System)
                /\ []ENABLED <<TD!DetectTermination>>_TD!vars
                => FALSE 
    BY PTL
  <2>1. TypeOK /\ ENABLED <<TD!DetectTermination>>_TD!vars
        => terminated /\ ~terminationDetected
    BY ExpandENABLED 
       DEF TypeOK, TD!DetectTermination, TD!vars, terminated, TD!terminated, terminationDetected
  <2>. QED BY <2>1, Live, PTL DEF Liveness
<1>. QED  
  BY <1>1, <1>2, <1>3, TypeCorrect, Invariant, PTL DEF Spec, TD!Spec
=============================================================================
\* Modification History
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz
