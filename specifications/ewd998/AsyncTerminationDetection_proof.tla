---------------------- MODULE AsyncTerminationDetection_proof ---------------------
(*********************************************************************************)
(* Proofs about the high-level specification of termination detection.           *)
(*********************************************************************************)

EXTENDS AsyncTerminationDetection, TLAPS

LEMMA TypeCorrect == Init /\ [][Next]_vars => []TypeOK
<1>. USE NAssumption DEF Node, TypeOK, terminated
<1>1. Init => TypeOK
  BY DEF Init, terminated
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF Next, vars, DetectTermination, Terminate, RcvMsg, SendMsg
<1>. QED BY <1>1, <1>2, PTL

(***************************************************************************)
(* Proofs of safety and stability.                                         *)
(***************************************************************************)
THEOREM Safety == Init /\ [][Next]_vars => []Safe
<1>. USE DEF terminated, TypeOK, Safe
<1>1. Init => Safe
  BY DEF Init
<1>2. TypeOK /\ Safe /\ [Next]_vars => Safe'
  BY DEF Next, vars, DetectTermination, Terminate, RcvMsg, SendMsg
<1>. QED
  BY <1>1, <1>2, TypeCorrect, PTL

THEOREM Stability == Init /\ [][Next]_vars => Quiescence
<1>. TypeOK /\ terminated /\ [Next]_vars => terminated'
    BY DEF TypeOK, terminated, Next, DetectTermination, Terminate, RcvMsg, SendMsg, vars
<1>. QED  BY TypeCorrect, PTL DEF Quiescence

(***************************************************************************)
(* Proofs of liveness.                                                     *)
(***************************************************************************)

(***************************************************************************)
(* We first reduce the enabledness condition that appears in the fairness  *)
(* hypothesis to a standard state predicate.                               *)
(***************************************************************************)
LEMMA EnabledDT == 
  ASSUME TypeOK 
  PROVE  (ENABLED <<DetectTermination>>_vars) <=> (terminated /\ ~ terminationDetected)
BY ExpandENABLED DEF TypeOK, DetectTermination, terminated, vars

THEOREM Liveness == Spec => Live
<1>. DEFINE P == terminated /\ ~ terminationDetected
            Q == terminationDetected
<1>1. TypeOK /\ P /\ [Next]_vars => P' \/ Q'
  BY DEF TypeOK, terminated, Next, vars, Terminate, SendMsg, RcvMsg, DetectTermination
<1>2. TypeOK /\ P /\ <<DetectTermination>>_vars => Q'
  BY DEF DetectTermination
<1>3. TypeOK /\ P => ENABLED <<DetectTermination>>_vars
  BY EnabledDT
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec, Live

=============================================================================
\* Modification History
\* Created Sun Jan 10 15:19:20 CET 2021 by merz
