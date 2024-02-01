\* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.
\*
\* Released under the terms of the Apache License 2.0
\* See: file LICENSE that came with this software for details.
\*
\* This file contains Intellectual Property that belongs to
\* Backyard Innovations Pte Ltd., Singapore.
\*
\* Authors: Santhosh Raju <santhosh@byisystems.com>
\*          Cherry G. Mathew <cherry@byisystems.com>
\*          Fransisca Andriani <sisca@byisystems.com>
\*
-------------------------- MODULE VoucherLifeCycle --------------------------
(***************************************************************************)
(* This specification is of a Voucher and it's life cycle. This is based   *)
(* on the definiton of Vouchers in RFC 3506 with the tuple part decoupled. *)
(*                                                                         *)
(* Note: A new state called "phantom" was introduced to indicate the state *)
(* of a voucher that is yet to be issued, once a voucher is issued it      *)
(* becomes a "valid" voucher. This is a one way transition and it cannot   *)
(* reversed.                                                               *)
(***************************************************************************)
CONSTANT V          \* The set of vouchers.

VARIABLE vState,    \* vState[v] is the state of a voucher v.
         vlcState   \* The state of the voucher life cycle machine.
                    \* vvlcState[v] is the state of the life cycle machine
                    \* for the voucher v.
-----------------------------------------------------------------------------
VTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VInit ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed on the Vs, and then     *)
(* define the complete next-state action of the specification to be the    *)
(* disjunction of the possible V actions.                                  *)
(***************************************************************************)
Issue(v)  ==
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

Transfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED <<vState, vlcState>>

Redeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Cancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext == \E v \in V : Issue(v) \/ Redeem(v) \/ Transfer(v) \/ Cancel(v)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
-----------------------------------------------------------------------------
VConsistent ==
  (*************************************************************************)
  (* A state predicate asserting that a V started at a valid start state   *)
  (* and has reached a valid final state at the end of the life cycle.     *)
  (* V can be "valid" only when the state of the machine is "working".     *)
  (* It is an invariant of the specification.                              *)
  (*************************************************************************)
  /\ \A v \in V : \/  /\ vlcState[v] = "done"
                      /\ vState[v] \in {"redeemed", "cancelled"}
                  \/  /\ vlcState[v] = "init"
                      /\ vState[v] = "phantom"
                  \/  /\ vlcState[v] = "working"
                      /\ vState[v] \in {"valid"}
-----------------------------------------------------------------------------
VSpec == VInit /\ [][VNext]_<<vState, vlcState>>
  (*************************************************************************)
  (* The complete specification of the protocol written as a temporal      *)
  (* formula.                                                              *)
  (*************************************************************************)

THEOREM VSpec => [](VTypeOK /\ VConsistent)
  (*************************************************************************)
  (* This theorem asserts the truth of the temporal formula whose meaning  *)
  (* is that the state predicate VTypeOK /\ VConsistent is an invariant    *)
  (* of the specification VSpec.  Invariance of this conjunction is        *)
  (* equivalent to invariance of both of the formulas VTypeOK and          *)
  (* VConsistent.                                                          *)
  (*************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue Jun 12 13:25:29 IST 2018 by Fox
\* Created Fri Mar 16 11:56:25 SGT 2018 by Fox
