-------------------------- MODULE MCDisruptor_SPMC --------------------------
(***************************************************************************)
(* Bounds Disruptor_SPMC for TLC.                                          *)
(*                                                                         *)
(* The producer in Disruptor_SPMC publishes forever, so its sequence       *)
(* numbers - and with them the history variable `consumed' - grow without  *)
(* bound.  MaxPublished caps how far the producer gets, which both makes   *)
(* the state space finite and makes Disruptor_SPMC!Liveliness checkable    *)
(* by turning its quantification over Nat into a finite conjunction.       *)
(***************************************************************************)

EXTENDS Disruptor_SPMC

CONSTANT
  MaxPublished  (* Max number of published events. Bounds the model. *)

ASSUME MaxPublishedIsPositive == MaxPublished \in Nat \ {0}

(***************************************************************************)
(* State constraint - bounds the model:                                    *)
(***************************************************************************)

StateConstraint == published < MaxPublished

(***************************************************************************)
(* Properties:                                                             *)
(***************************************************************************)

(* Eventually always, consumers must have read all published values.       *)
(*                                                                         *)
(* This lives here rather than in Disruptor_SPMC because the range of i is *)
(* a model bound.  Note that TLC checks it on the state graph pruned by    *)
(* StateConstraint, where a behavior may end in a state whose successors   *)
(* were all pruned; a liveness result under a state constraint is thus     *)
(* weaker than it appears.                                                 *)
Liveliness ==
  \A r \in Readers : \A i \in 0 .. (MaxPublished - 1) :
    <>[](i \in 0 .. published => Len(consumed[r]) >= i + 1 /\ consumed[r][i + 1] = i)

=============================================================================
