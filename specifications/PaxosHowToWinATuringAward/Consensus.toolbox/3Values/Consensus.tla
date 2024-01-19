----------------------------- MODULE Consensus ------------------------------ 
(***************************************************************************)
(* This is an very abstract specification of the consensus problem, in     *)
(* which a set of processes must choose a single value.  We abstract away  *)
(* even the processes.  We specify the simple requirement that at most one *)
(* value is chosen by describing the set of all chosen values.  The naive  *)
(* requirement is that this set never contains more than one value, which  *)
(* is an invariance property.  But a little thought shows that this        *)
(* requirement allows a value to be chosen then unchosen, and then another *)
(* value to be chosen.  So we specify that the set of chosen values is     *)
(* initially empty, it can be set to a single value, and then it can never *)
(* change.                                                                 *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets
  (*************************************************************************)
  (* Imports standard modules that define operators of arithmetic on       *)
  (* natural numbers and the Cardinality operator, where Cardinality(S) is *)
  (* the number of elements in the set S, if S is finite.                  *)
  (*************************************************************************)
CONSTANT Value 
  (*************************************************************************)
  (* The set of all values that can be chosen.                             *)
  (*************************************************************************)
VARIABLE chosen
  (*************************************************************************)
  (* The set of all values that have been chosen.                          *)
  (*************************************************************************)

(***************************************************************************)
(* The type-correctness invariant asserting the "type" of the variable     *)
(* 'chosen'.  It isn't part of the spec itself--that is, the formula       *)
(* describing the possible sequence of values that 'chosen' can have in a  *)
(* behavior correct behavior of the system, but is an invariance property  *)
(* that the spec should satisfy.                                           *)
(***************************************************************************)
TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen) 

(***************************************************************************)
(* The initial predicate describing the possible initial state of          *)
(* 'chosen'.                                                               *)
(***************************************************************************)
Init == chosen = {}

(***************************************************************************)
(* The next-state relation describing how 'chosen' can change from one     *)
(* step to the next.  Note that is enabled (equals true for some next      *)
(* value chosen' of choseen) if and only if chosen equals the empty set.   *)
(***************************************************************************)
Next == /\ chosen = {}
        /\ \E v \in Value : chosen' = {v}

(***************************************************************************)
(* The TLA+ temporal formula that is the spec.                             *)
(***************************************************************************)
Spec == Init /\ [][Next]_chosen 

-----------------------------------------------------------------------------
(***************************************************************************)
(* The specification should imply the safety property that 'chosen' can    *)
(* contain at most one value in any reachable state.  This condition on    *)
(* the state is expressed by Inv defined here.                             *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

(***************************************************************************)
(* You can now run the TLC model checker on the model named 3Values to     *)
(* check that Inv is an invariant, meaning that it's true of every         *)
(* reachable state.  TLC's default setting to check for deadlock would     *)
(* cause it to report a deadlock because no action is possible after a     *)
(* value is chosen.  We would say that the system terminated, but          *)
(* termination is just deadlock that we want to happen, and we have to     *)
(* tell TLC that we want deadlock by disabling its check for it.           *)
(***************************************************************************)


(***************************************************************************)
(* The following theorem asserts the desired safety propert.  Its proof    *)
(* appears after the theorem.  This proof is easily checked by the TLAPS   *)
(* prover.                                                                 *)
(***************************************************************************)
THEOREM Invariance  ==  Spec => []Inv
<1>1. Init => Inv

<1>2. Inv /\ [Next]_chosen  => Inv'

<1>3. QED
  BY <1>1, <1>2 DEF Spec
=============================================================================
