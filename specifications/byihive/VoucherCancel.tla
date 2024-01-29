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
--------------------------- MODULE VoucherCancel ----------------------------
(***************************************************************************)
(* This specification describes the cancellation of Voucher between an     *)
(* Issuer and a Holder. It is implemented over the Two-Phase Commit        *)
(* protocol, in which a Voucher Transaction Provider (VTP) coordinates the *)
(* Voucher Issuers (Is) to cancel vouchers (Vs) to Voucher Holders (Hs) as *)
(* described in the VoucherLifeCycle specification module. In this         *)
(* specification, Hs and Is spontaneously issue Prepared messages. We      *)
(* ignore the Prepare messages that the VTP can send to the Hs and Is.     *)
(*                                                                         *)
(* For simplicity, we also eliminate Abort messages sent by an Hs / Is     *)
(* when it decides to abort.  Such a message would cause the VTP to abort  *)
(* the transaction, an event represented here by the VTP spontaneously     *)
(* deciding to abort.                                                      *)
(*                                                                         *)
(* Note: This operation is an addendum to the operations described in RFC  *)
(* 3506. This operation is not described in the RFC.                       *)
(***************************************************************************)
CONSTANT
    V,             \* The set of Vouchers
    H,             \* The set of Voucher Holders
    I              \* The set of Voucher Issuers

VARIABLES
  vState,          \* vState[v] is the state of voucher v.
  vlcState,        \* vlcState[v] is the state of the voucher life cycle
                   \* machine.
  hState,          \* hState[h] is the state of voucher holder h.
  iState,          \* iState[i] is the state of voucher issuer i.
  vtpState,        \* The state of the voucher transaction provider.
  vtpCPrepared,    \* The set of Hs and Is from which the VTP has received
                   \* "Prepared for Voucher Cancel" messages.
  msgs
    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  For simplicity, we represent message passing with the    *)
    (* variable msgs whose value is the set of all messages that have been *)
    (* sent.  A message is sent by adding it to the set msgs.  An action   *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the presence of that message in  *)
    (* msgs.  For simplicity, messages are never removed from msgs.  This  *)
    (* allows a single message to be received by multiple receivers.       *)
    (* Receipt of the same message twice is therefore allowed; but in this *)
    (* particular protocol, that's not a problem.                          *)
    (***********************************************************************)

Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the H indicated by the message's vh field to the VTP.       *)
  (* Similar "Prepared" is also sent from I indicated by message's vc      *)
  (* field to the VTP. Messages of type "Cancel" and "Abort" are broadcast *)
  (* by the VTPs, to be received by all Hs and Is.  The set msgs contains  *)
  (* just a single copy of such a message.                                 *)
  (*************************************************************************)
  [type : {"Prepared"}, vh : H] \cup
  [type : {"Prepared"}, vi : I] \cup
  [type : {"Cancel", "Abort"}]

VTPTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ vState \in [V -> {"valid", "cancelled"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
  /\ iState \in [I -> {"waiting", "prepared", "cancelled", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpCPrepared \subseteq (H \cup I)
  /\ msgs \subseteq Messages

VTPInit ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState = [h \in H |-> "holding"]
  /\ iState = [i \in I |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpCPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the VTP's actions, the Hs' actions, then the Is' actions.               *)
(***************************************************************************)
VTPRcvPrepared(h,i) ==
  (*************************************************************************)
  (* The VTP receives a "Prepared" message from Voucher Holder h and the   *)
  (* Voucher Issuer i. We could add the additional enabling condition      *)
  (* h,i \notin vtpCPrepared, which disables the action if the VTP has     *)
  (* already received this message. But there is no need, because in that  *)
  (* case the action has no effect; it leaves the state unchanged.         *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ [type |-> "Prepared", vi |-> i] \in msgs
  /\ vtpCPrepared' = vtpCPrepared \cup {h,i}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPCancel(v) ==
  (*************************************************************************)
  (* The VTP Cancels the voucher; enabled iff the VTP is in its            *)
  (* initial state and every H and I has sent a "Prepared" message.        *)
  (*************************************************************************)
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState = "init"
  /\ vtpCPrepared = H \cup I
  /\ vtpState' = "done"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs' = msgs \cup {[type |-> "Cancel"]}
  /\ UNCHANGED <<hState, iState, vtpCPrepared>>

VTPAbort(v) ==
  (*************************************************************************)
  (* The VTP spontaneously aborts the transaction.                         *)
  (*************************************************************************)
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpCPrepared>>

HPrepare(h) ==
  (*************************************************************************)
  (* Voucher holder h prepares.                                            *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED <<vState, vlcState, vtpState, iState, vtpCPrepared>>

HChooseToAbort(h) ==
  (*************************************************************************)
  (* Voucher holder h spontaneously decides to abort.  As noted above, h   *)
  (* does not send any message in our simplified spec.                     *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, vtpState, iState, vtpCPrepared, msgs>>

HRcvCancelMsg(h) ==
  (*************************************************************************)
  (* Voucher holder h is told by the VTP to Cancel.                        *)
  (*************************************************************************)
  /\ vState \in [V -> {"valid", "cancelled"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ hState[h] = "holding"
  /\ [type |-> "Cancel"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "cancelled"]
  /\ UNCHANGED <<vtpState, vState, vlcState, iState, vtpCPrepared, msgs>>

HRcvAbortMsg(h) ==
  (*************************************************************************)
  (* Voucher holder h is told by the VTP to abort.                         *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState[h] = "holding"
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, vtpState, iState, vtpCPrepared, msgs>>

IPrepare(i) ==
  (*************************************************************************)
  (* Voucher issuer i prepares.                                            *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
  /\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpCPrepared>>

IChooseToAbort(i) ==
  (*************************************************************************)
  (* Voucher issuer i spontaneously decides to abort. As noted above, i    *)
  (* does not send any message in our simplified spec.                     *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpCPrepared, msgs>>

IRcvCancelMsg(i) ==
  (*************************************************************************)
  (* Voucher issuer i is told by the VTP to Cancel.                        *)
  (*************************************************************************)
  /\ vState \in [V -> {"valid", "cancelled"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ iState[i] = "waiting"
  /\ [type |-> "Cancel"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "cancelled"]
  /\ UNCHANGED <<vtpState, vState, vlcState, hState, vtpCPrepared, msgs>>

IRcvAbortMsg(i) ==
  (*************************************************************************)
  (* Voucher issuer i is told by the VTP to abort.                         *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ iState[i] = "waiting"
  /\ [type |-> "Abort"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpCPrepared, msgs>>

VTPNext ==
  \/ \E v \in V:
       VTPCancel(v) \/ VTPAbort(v)
  \/ \E h,i \in H \cup I:
       VTPRcvPrepared(h,i)
  \/ \E h \in H:
       HPrepare(h) \/ HChooseToAbort(h)
       \/ HRcvAbortMsg(h) \/ HRcvCancelMsg(h)
  \/ \E i \in I:
       IPrepare(i) \/ IChooseToAbort(i)
       \/ IRcvAbortMsg(i) \/ IRcvCancelMsg(i)
-----------------------------------------------------------------------------
VTPConsistent ==
  (*************************************************************************)
  (* A state predicate asserting that a H and an I have not reached        *)
  (* conflicting decisions. It is an invariant of the specification.       *)
  (*************************************************************************)
  /\ \A h \in H, i \in I :   /\ ~ /\ hState[h] = "cancelled"
                                  /\ iState[i] = "aborted"
                             /\ ~ /\ hState[h] = "aborted"
                                  /\ iState[i] = "cancelled"
-----------------------------------------------------------------------------
VTPVars == <<hState, iState, vState, vlcState, vtpState, vtpCPrepared, msgs>>

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars
  (*************************************************************************)
  (* The complete spec of the a Voucher Cancel using Two-Phase Commit      *)
  (* protocol.                                                             *)
  (*************************************************************************)

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)
  (*************************************************************************)
  (* This theorem asserts the truth of the temporal formula whose meaning  *)
  (* is that the state predicate VTPTypeOK /\ VTPConsistent is an          *)
  (* invariant of the specification VTPSpec. Invariance of this            *)
  (* conjunction is equivalent to invariance of both of the formulas       *)
  (* VTPTypeOK and VTPConsistent.                                          *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert that the Voucher Cancel specification implements the      *)
(* Voucher Life Cycle specification of a voucher mentioned in module       *)
(* VoucherLifeCycle. The following statement imports all the definitions   *)
(* from module VoucherLifeCycle into the current module.                   *)
(***************************************************************************)
INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VSpec
  (*************************************************************************)
  (* This theorem asserts that the specification VTPSpec of the Two-Phase  *)
  (* Commit protocol implements the specification VSpec of the             *)
  (* Voucher life cycle specification.                                     *)
  (*************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue Jun 12 13:03:21 IST 2018 by Fox
\* Created Fri Mar 16 17:45:37 SGT 2018 by Fox
