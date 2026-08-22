-------------------------- MODULE MCDisruptor_MPMC --------------------------
(***************************************************************************)
(* Bounds Disruptor_MPMC for TLC.                                          *)
(*                                                                         *)
(* The producers in Disruptor_MPMC publish forever, so the claimed         *)
(* sequence numbers - and with them the history variable `consumed' -      *)
(* grow without bound.  MaxPublished caps how many sequence numbers are    *)
(* claimed, which both makes the state space finite and makes              *)
(* Disruptor_MPMC!Liveliness checkable by turning its quantification over  *)
(* Nat into a finite conjunction.                                          *)
(***************************************************************************)

EXTENDS Disruptor_MPMC

CONSTANT
  MaxPublished      (* Max number of published events. Bounds the model.    *)

ASSUME MaxPublishedIsPositive == MaxPublished \in Nat \ {0}

(***************************************************************************)
(* State constraint - bounds the model:                                    *)
(***************************************************************************)

StateConstraint == next_sequence <= MaxPublished

(***************************************************************************)
(* Properties:                                                             *)
(***************************************************************************)

(* Eventually always, consumers must have read all published values.       *)
(*                                                                         *)
(* This lives here rather than in Disruptor_MPMC because the range of i is *)
(* a model bound.  Note that TLC checks it on the state graph pruned by    *)
(* StateConstraint, where a behavior may end in a state whose successors   *)
(* were all pruned; a liveness result under a state constraint is thus     *)
(* weaker than it appears.                                                 *)
Liveliness ==
  \A r \in Readers : \A i \in 0..(MaxPublished - 1) :
    <>[](i \in 0..AvailablePublishedSequence => Len(consumed[r]) >= i + 1 /\ consumed[r][i + 1] = i)

=============================================================================
