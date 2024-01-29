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
--------------------------- MODULE VoucherRedeem ----------------------------
(***************************************************************************)
(* The description is based on the "Redeem" operation mentioned in RFC     *)
(* 3506. This specification describes the redemption of Voucher between    *)
(* a Holder and Collector. It is implemented over the Two-Phase Commit     *)
(* protocol, in which a Voucher Transaction Provider (VTP) coordinates the *)
(* Voucher Holders (Hs) to redeem vouchers (Vs) to Voucher Collectors (Cs) *)
(* described in the VoucherLifeCycle specification module. In this         *)
(* specification, Hs and Cs spontaneously issue Prepared messages. We      *)
(* ignore the Prepare messages that the VTP can send to the Hs and Cs.     *)
(*                                                                         *)
(* For simplicity, we also eliminate Abort messages sent by an Hs / Cs     *)
(* when it decides to abort.  Such a message would cause the VTP to abort  *)
(* the transaction, an event represented here by the VTP spontaneously     *)
(* deciding to abort.                                                      *)
(***************************************************************************)
CONSTANT
    V,             \* The set of Vouchers
    H,             \* The set of Voucher Holders
    C              \* The set of Voucher Collectors

VARIABLES
  vState,          \* vState[v] is the state of voucher v.
  vlcState,        \* vlcState[v] is the state of the voucher life cycle
                   \* machine.
  hState,          \* hState[h] is the state of voucher holder h.
  cState,          \* cState[c] is the state of voucher collector c.
  vtpState,        \* The state of the voucher transaction provider.
  vtpRPrepared,    \* The set of Hs and Cs from which the VTP has received
                   \* "Prepared for Voucher Redeem" messages.
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
  (* Similar "Prepared" is also sent from C indicated by message's vc      *)
  (* field to the VTP. Messages of type "Redeem" and "Abort" are broadcast *)
  (* by the VTPs, to be received by all Hs and Cs.  The set msgs contains  *)
  (* just a single copy of such a message.                                 *)
  (*************************************************************************)
  [type : {"Prepared"}, vh : H] \cup
  [type : {"Prepared"}, vc : C] \cup
  [type : {"Redeem", "Abort"}]

VTPTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ vState \in [V -> {"valid", "redeemed"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ hState \in [H -> {"holding", "prepared", "redeemed", "aborted"}]
  /\ cState \in [C -> {"waiting", "prepared", "redeemed", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpRPrepared \subseteq (H \cup C)
  /\ msgs \subseteq Messages

VTPInit ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState = [h \in H |-> "holding"]
  /\ cState = [c \in C |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpRPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the VTP's actions, the Hs' actions, then the Cs' actions.               *)
(***************************************************************************)
VTPRcvPrepared(h,c) ==
  (*************************************************************************)
  (* The VTP receives a "Prepared" message from Voucher Holder h and the   *)
  (* Voucher Collector c. We could add the additional enabling condition   *)
  (* h,c \notin vtpRPrepared, which disables the action if the VTP has     *)
  (* already received this message. But there is no need, because in that  *)
  (* case the action has no effect; it leaves the state unchanged.         *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ [type |-> "Prepared", vc |-> c] \in msgs
  /\ vtpRPrepared' = vtpRPrepared \cup {h,c}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpState, msgs>>

VTPRedeem(v) ==
  (*************************************************************************)
  (* The VTP Redeems the voucher; enabled iff the VTP is in its            *)
  (* initial state and every H and C has sent a "Prepared" message.        *)
  (*************************************************************************)
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState = "init"
  /\ vtpRPrepared = H \cup C
  /\ vtpState' = "done"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs' = msgs \cup {[type |-> "Redeem"]}
  /\ UNCHANGED <<hState, cState, vtpRPrepared>>

VTPAbort(v) ==
  (*************************************************************************)
  (* The VTP spontaneously aborts the transaction.                         *)
  (*************************************************************************)
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpRPrepared>>

HPrepare(h) ==
  (*************************************************************************)
  (* Voucher holder h prepares.                                            *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED <<vState, vlcState, vtpState, cState, vtpRPrepared>>

HChooseToAbort(h) ==
  (*************************************************************************)
  (* Voucher holder h spontaneously decides to abort.  As noted above, h   *)
  (* does not send any message in our simplified spec.                     *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, vtpState, cState, vtpRPrepared, msgs>>

HRcvRedeemMsg(h) ==
  (*************************************************************************)
  (* Voucher holder h is told by the VTP to Redeem.                        *)
  (*************************************************************************)
  /\ vState \in [V -> {"valid", "redeemed"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ hState[h] = "holding"
  /\ [type |-> "Redeem"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "redeemed"]
  /\ UNCHANGED <<vtpState, vState, vlcState, cState, vtpRPrepared, msgs>>

HRcvAbortMsg(h) ==
  (*************************************************************************)
  (* Voucher holder h is told by the VTP to abort.                         *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState[h] = "holding"
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, vtpState, cState, vtpRPrepared, msgs>>

CPrepare(c) ==
  (*************************************************************************)
  (* Voucher collector c prepares.                                         *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ cState[c] = "waiting"
  /\ cState' = [cState EXCEPT ![c] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vc |-> c]}
  /\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpRPrepared>>

CChooseToAbort(c) ==
  (*************************************************************************)
  (* Voucher collector c spontaneously decides to abort. As noted above, c *)
  (* does not send any message in our simplified spec.                     *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ cState[c] = "waiting"
  /\ cState' = [cState EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpRPrepared, msgs>>

CRcvRedeemMsg(c) ==
  (*************************************************************************)
  (* Voucher collector c is told by the VTP to Redeem.                     *)
  (*************************************************************************)
  /\ vState \in [V -> {"valid", "redeemed"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ cState[c] = "waiting"
  /\ [type |-> "Redeem"] \in msgs
  /\ cState' = [cState EXCEPT ![c] = "redeemed"]
  /\ UNCHANGED <<vtpState, vState, vlcState, hState, vtpRPrepared, msgs>>

CRcvAbortMsg(c) ==
  (*************************************************************************)
  (* Voucher collector c is told by the VTP to abort.                      *)
  (*************************************************************************)
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ cState[c] = "waiting"
  /\ [type |-> "Abort"] \in msgs
  /\ cState' = [cState EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpRPrepared, msgs>>

VTPNext ==
  \/ \E v \in V:
       VTPRedeem(v) \/ VTPAbort(v)
  \/ \E h,c \in H \cup C:
       VTPRcvPrepared(h,c)
  \/ \E h \in H:
       HPrepare(h) \/ HChooseToAbort(h)
       \/ HRcvAbortMsg(h) \/ HRcvRedeemMsg(h)
  \/ \E c \in C:
       CPrepare(c) \/ CChooseToAbort(c)
       \/ CRcvAbortMsg(c) \/ CRcvRedeemMsg(c)
-----------------------------------------------------------------------------
VTPConsistent ==
  (*************************************************************************)
  (* A state predicate asserting that a H and an C have not reached        *)
  (* conflicting decisions. It is an invariant of the specification.       *)
  (*************************************************************************)
  /\ \A h \in H, c \in C :   /\ ~ /\ hState[h] = "redeemed"
                                  /\ cState[c] = "aborted"
                             /\ ~ /\ hState[h] = "aborted"
                                  /\ cState[c] = "redeemed"
-----------------------------------------------------------------------------
VTPVars == <<hState, cState, vState, vlcState, vtpState, vtpRPrepared, msgs>>

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars
  (*************************************************************************)
  (* The complete spec of the a Voucher Redeem using Two-Phase Commit      *)
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
(* We now assert that the Voucher Redeem specification implements the      *)
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
\* Last modified Tue Jun 12 13:35:49 IST 2018 by Fox
\* Created Fri Mar 16 17:45:37 SGT 2018 by Fox
