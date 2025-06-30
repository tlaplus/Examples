------------------- MODULE SyncTerminationDetection_proof -------------------
(***************************************************************************)
(* Proofs of the properties asserted in module SyncTerminationDetection.   *)
(***************************************************************************)
EXTENDS SyncTerminationDetection, TLAPS

(* Proofs of safety properties *)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, terminated
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY DEF Next, Terminate, Wakeup, DetectTermination, vars, terminated, TypeOK
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

THEOREM CorrectDetection == Spec => TDCorrect
<1>1. Init => TDCorrect 
  BY DEF Init, TDCorrect
<1>2. TypeOK /\ TDCorrect /\ [Next]_vars => TDCorrect' 
  BY DEF TDCorrect, Next, Terminate, Wakeup, 
         DetectTermination, vars, terminated, TypeOK
<1>. QED  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec

THEOREM Quiescent == Spec => Quiescence
<1>. TypeOK /\ [Next]_vars => (terminated => terminated')
  BY DEF TypeOK, terminated, Next, Terminate, Wakeup, 
         DetectTermination, vars
<1>. QED  BY TypeCorrect, PTL DEF Spec, Quiescence

------------------------------------------------------------------------------
(* Proof of liveness *)

(****************************************************************************)
(* The following lemma reduces the enabledness condition underlying the     *)
(* fairness condition to a simple state predicate.                          *)
(****************************************************************************)
LEMMA Enabled_ST == 
    ASSUME TypeOK
    PROVE (ENABLED <<DetectTermination>>_vars) <=> terminated /\ ~terminationDetected
BY ExpandENABLED DEF TypeOK, DetectTermination, terminated, vars

(****************************************************************************)
(* Proving liveness is easy since a single occurrence of the helpful action *)
(* DetectTermination leads to the desired state.                            *)
(****************************************************************************)
THEOREM Live == Spec => Liveness
<1>. DEFINE P == terminated /\ ~terminationDetected
            Q == terminationDetected
<1>1. TypeOK /\ P /\ [Next]_vars => P' \/ Q'
  BY DEF TypeOK, Next, Terminate, Wakeup, DetectTermination, vars, terminated
<1>2. TypeOK /\ P /\ <<DetectTermination>>_vars => Q'
  BY DEF TypeOK, DetectTermination
<1>3. TypeOK /\ P => ENABLED <<DetectTermination>>_vars
  BY Enabled_ST
<1>. QED  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec, Liveness

=============================================================================
