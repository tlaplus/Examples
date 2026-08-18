--------------------------- MODULE FlashWithMutexCMP ---------------------------
(****************************************************************************)
(* The CMP encoding of flashWithMutex.m, after the method of Chou, Mannava  *)
(* and Park: keep the nodes in NODE concrete, summarize all other nodes in  *)
(* one node `Other`, and let the ABS_* rules stand in for them.  Those      *)
(* rules cannot see a summarized node's local state, which is not modelled, *)
(* so they are more non-deterministic than the rules they replace.          *)
(*                                                                          *)
(* One finite model is then meant to say something about every node count,  *)
(* which is how flashWithMutex.m was checked: Murphi fixes one NODE_NUM per *)
(* run just as TLC fixes one NODE.  That it does say anything is not        *)
(* established here -- it would need every behaviour of FlashWithMutex, at  *)
(* any node count, to be a behaviour of this module, and no such refinement *)
(* is stated, let alone proved.  The encoding may under-approximate just as *)
(* easily as over-approximate.                                              *)
(*                                                                          *)
(* It is kept apart from FlashWithMutex because the protocol does not need  *)
(* it: NODE is a CONSTANT there, so TLAPS can reason about all sizes at     *)
(* once instead of one at a time.                                           *)
(*                                                                          *)
(* Three definitions are restated rather than inherited.  ABS_TypeOK widens *)
(* the six fields that hold a node pointer, since each may now point at     *)
(* `Other`; the directory's sharer sets are not among them, `Other` never   *)
(* being recorded as a sharer.  CMPNext subtracts the one inherited step    *)
(* that would record it and adds the ABS_* rules.  CMPFairness re-forms the *)
(* weak fairness groups, because a message slot the summarized nodes answer *)
(* is only served if its ABS_* responder is fair too.                       *)
(****************************************************************************)
EXTENDS FlashWithMutex

CONSTANT Other   \* the abstract CMP node (enum{Other})

ASSUME OtherNotInNODE == Other \notin NODE
ASSUME OtherNotInDATA == Other \notin DATA
ASSUME UndefNotOther  == Undefined # Other

ABS_NODE  == NODE \cup {Other}
ABS_NodeU == ABS_NODE \cup {Undefined}

-------------------------------------------------------------------------------

\* TypeOK with every node-pointer field widened by the abstract node.  The
\* directory's ShrSet and InvSet stay subsets of NODE.
ABS_TypeOK ==
    /\ Home \in NODE
    /\ Proc \in [NODE -> [ProcCmd : NODE_CMD, InvMarked : BOOLEAN,
                          CacheState : CACHE_STATE, CacheData : DataU]]
    /\ Dir \in [Pending : BOOLEAN, Local : BOOLEAN, Dirty : BOOLEAN,
                HeadVld : BOOLEAN, HeadPtr : ABS_NodeU, ShrVld : BOOLEAN,
                ShrSet : SUBSET NODE, InvSet : SUBSET NODE]
    /\ MemData \in DATA
    /\ UniMsg \in [NODE -> [Cmd : UNI_CMD, Proc : ABS_NodeU, Data : DataU]]
    /\ InvMsg \in [NODE -> [Cmd : INV_CMD]]
    /\ RpMsg  \in [NODE -> [Cmd : RP_CMD]]
    /\ WbMsg   \in [Cmd : WB_CMD, Proc : ABS_NodeU, Data : DataU]
    /\ ShWbMsg \in [Cmd : SHWB_CMD, Proc : ABS_NodeU, Data : DataU]
    /\ NakcMsg \in [Cmd : NAKC_CMD]
    /\ CurrData \in DATA
    /\ PrevData \in DATA
    /\ PendReqSrc \in ABS_NodeU
    /\ PendReqCmd \in UniU
    /\ Collecting \in BOOLEAN
    /\ FwdCmd \in UNI_CMD
    /\ FwdSrc \in ABS_NodeU

-------------------------------------------------------------------------------
(*                    ABS_* abstract-environment rules                       *)
-------------------------------------------------------------------------------
(* Shared guard fragment used by the ABS_* rules that summarize a writeback  *)
(* from the abstract node (Lemma_1 side condition).                          *)

AbsDirtyClean ==
    /\ Dir.Dirty
    /\ WbMsg.Cmd # "WB_Wb"
    /\ ShWbMsg.Cmd # "SHWB_ShWb"
    /\ \A p \in NODE : Proc[p].CacheState # "CACHE_E"
    /\ UniMsg[Home].Cmd # "UNI_Put"
    /\ \A q \in NODE : UniMsg[q].Cmd # "UNI_PutX"

ABS_Store(data) ==
    /\ AbsDirtyClean
    /\ CurrData' = data
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg,
                   NakcMsg, PrevData, pendVars, fwdVars>>

ABS_PI_Remote_PutX ==
    /\ AbsDirtyClean
    /\ WbMsg' = [Cmd |-> "WB_Wb", Proc |-> Other, Data |-> CurrData]
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

ABS_NI_Local_Get_Get ==
    /\ ~Dir.Pending /\ Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr # Other
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_Get" ELSE FwdCmd
    /\ PendReqSrc' = Other
    /\ PendReqCmd' = "UNI_Get"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, FwdSrc>>

ABS_NI_Local_Get_Put ==
    /\ ~Dir.Pending
    /\ (Dir.Dirty => (Dir.Local /\ Proc[Home].CacheState = "CACHE_E"))
    /\ Dir' = IF Dir.Dirty
              THEN [Dir EXCEPT !.Dirty = FALSE, !.HeadVld = TRUE, !.HeadPtr = Other]
              ELSE IF Dir.HeadVld
                   THEN [Dir EXCEPT !.ShrVld = TRUE, !.InvSet = Dir.ShrSet]
                   ELSE [Dir EXCEPT !.HeadVld = TRUE, !.HeadPtr = Other]
    /\ MemData' = IF Dir.Dirty THEN Proc[Home].CacheData ELSE MemData
    /\ Proc' = IF Dir.Dirty THEN [Proc EXCEPT ![Home].CacheState = "CACHE_S"] ELSE Proc
    /\ UNCHANGED <<Home, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars>>

\* Abstract remote NAK, source side (merges the former ABS_NI_Remote_Get_Nak_src
\* / ABS_NI_Remote_GetX_Nak_src).
ABS_NI_Remote_Nak_src(dst) ==
    /\ dst # Home
    /\ Proc[dst].CacheState # "CACHE_E"
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd \in {"UNI_Get", "UNI_GetX"}
    /\ NakcMsg' = [Cmd |-> "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg,
                   CurrData, PrevData, pendVars>>

ABS_NI_Remote_Get_Nak_dst(src) ==
    /\ UniMsg[src].Cmd = "UNI_Get" /\ UniMsg[src].Proc = Other
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = src /\ FwdCmd = "UNI_Get"
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Nak", Proc |-> Other, Data |-> Undefined]]
    /\ NakcMsg' = [Cmd |-> "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, CurrData,
                   PrevData, pendVars>>

\* Abstract remote NAK, both sides abstract (merges the former
\* ABS_NI_Remote_Get_Nak_src_dst / ABS_NI_Remote_GetX_Nak_src_dst).
ABS_NI_Remote_Nak_src_dst ==
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd \in {"UNI_Get", "UNI_GetX"}
    /\ NakcMsg' = [Cmd |-> "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg,
                   CurrData, PrevData, pendVars>>

ABS_NI_Remote_Get_Put_src(dst) ==
    /\ dst # Home
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd = "UNI_Get"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_S"]
    /\ ShWbMsg' = [Cmd |-> "SHWB_ShWb", Proc |-> Other, Data |-> Proc[dst].CacheData]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars>>

ABS_NI_Remote_Get_Put_dst(src) ==
    /\ UniMsg[src].Cmd = "UNI_Get" /\ UniMsg[src].Proc = Other
    /\ AbsDirtyClean
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = src /\ FwdCmd = "UNI_Get"
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Put", Proc |-> Other, Data |-> CurrData]]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ ShWbMsg' = IF src # Home
                  THEN [Cmd |-> "SHWB_ShWb", Proc |-> src, Data |-> CurrData]
                  ELSE ShWbMsg
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars>>

ABS_NI_Remote_Get_Put_src_dst ==
    /\ AbsDirtyClean
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd = "UNI_Get"
    /\ ShWbMsg' = [Cmd |-> "SHWB_ShWb", Proc |-> Other, Data |-> CurrData]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg,
                   CurrData, PrevData, pendVars>>

ABS_NI_Local_GetX_GetX ==
    /\ ~Dir.Pending /\ Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr # Other
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_GetX" ELSE FwdCmd
    /\ PendReqSrc' = Other
    /\ PendReqCmd' = "UNI_GetX"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, FwdSrc>>

\* Home holds the line exclusively; the abstract node takes it over.
ABS_NI_Local_GetX_PutX_Dirty ==
    /\ Dir.Dirty
    /\ Dir' = [Dir EXCEPT !.Local = FALSE, !.Dirty = TRUE, !.HeadVld = TRUE,
                          !.HeadPtr = Other, !.ShrVld = FALSE, !.ShrSet = {}, !.InvSet = {}]
    /\ Proc' = ProcHomeInvalid
    /\ UNCHANGED <<InvMsg, PrevData, pendVars>>

\* The abstract node is already the head and no concrete node shares the line.
ABS_NI_Local_GetX_PutX_Grant ==
    /\ ~Dir.Dirty
    /\ NoOtherSharers(Other)
    /\ Dir' = [Dir EXCEPT !.Local = FALSE, !.Dirty = TRUE, !.HeadVld = TRUE,
                          !.HeadPtr = Other, !.ShrVld = FALSE, !.ShrSet = {}, !.InvSet = {}]
    /\ Proc' = IF Dir.Local THEN ProcHomeInvalidMarked ELSE ProcHomeInvalid
    /\ UNCHANGED <<InvMsg, PrevData, pendVars>>

\* Concrete nodes share the line: they are invalidated first.
ABS_NI_Local_GetX_PutX_Inv ==
    /\ ~Dir.Dirty
    /\ ~NoOtherSharers(Other)
    /\ Dir' = [Pending |-> TRUE, Local |-> FALSE, Dirty |-> TRUE, HeadVld |-> TRUE,
               HeadPtr |-> Other, ShrVld |-> FALSE, ShrSet |-> {}, InvSet |-> InvNodes({Home})]
    /\ Proc' = IF Dir.Local THEN ProcHomeInvalidMarked ELSE Proc
    /\ InvMsg' = [p \in NODE |-> [Cmd |-> IF p \in InvNodes({Home})
                                          THEN "INV_Inv" ELSE "INV_None"]]
    /\ PendReqSrc' = Other
    /\ PendReqCmd' = "UNI_GetX"
    /\ Collecting' = TRUE
    /\ PrevData' = CurrData

ABS_NI_Local_GetX_PutX ==
    /\ ~Dir.Pending
    /\ (Dir.Dirty => (Dir.Local /\ Proc[Home].CacheState = "CACHE_E"))
    /\ \/ ABS_NI_Local_GetX_PutX_Dirty
       \/ ABS_NI_Local_GetX_PutX_Grant
       \/ ABS_NI_Local_GetX_PutX_Inv
    /\ UNCHANGED <<Home, MemData, UniMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   fwdVars>>

ABS_NI_Remote_GetX_Nak_dst(src) ==
    /\ UniMsg[src].Cmd = "UNI_GetX" /\ UniMsg[src].Proc = Other
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = src /\ FwdCmd = "UNI_GetX"
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Nak", Proc |-> Other, Data |-> Undefined]]
    /\ NakcMsg' = [Cmd |-> "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, CurrData,
                   PrevData, pendVars>>

ABS_NI_Remote_GetX_PutX_src(dst) ==
    /\ dst # Home
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd = "UNI_GetX"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_I", ![dst].CacheData = Undefined]
    /\ ShWbMsg' = [Cmd |-> "SHWB_FAck", Proc |-> Other, Data |-> Undefined]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars>>

ABS_NI_Remote_GetX_PutX_dst(src) ==
    /\ UniMsg[src].Cmd = "UNI_GetX" /\ UniMsg[src].Proc = Other
    /\ AbsDirtyClean
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = src /\ FwdCmd = "UNI_GetX"
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_PutX", Proc |-> Other, Data |-> CurrData]]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ ShWbMsg' = IF src # Home
                  THEN [Cmd |-> "SHWB_FAck", Proc |-> src, Data |-> Undefined]
                  ELSE ShWbMsg
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars>>

ABS_NI_Remote_GetX_PutX_src_dst ==
    /\ AbsDirtyClean
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd = "UNI_GetX"
    /\ ShWbMsg' = [Cmd |-> "SHWB_FAck", Proc |-> Other, Data |-> Undefined]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg,
                   CurrData, PrevData, pendVars>>

\* All concrete nodes have acked: the round closes and the request retires.
\* The Murphi rule also fires while acks are still outstanding, but that branch
\* assigns nothing except the dropped ghosts LastInvAck and LastOtherInvAck, so
\* here it would be a stuttering step and is left out.
ABS_NI_InvAck ==
    /\ Dir.Pending /\ Collecting
    /\ Dir.InvSet = {}
    /\ NakcMsg.Cmd = "NAKC_None" /\ ShWbMsg.Cmd = "SHWB_None"
    /\ \A q \in NODE :
         /\ ((UniMsg[q].Cmd = "UNI_Get" \/ UniMsg[q].Cmd = "UNI_GetX")
                => UniMsg[q].Proc = Home)
         /\ (UniMsg[q].Cmd = "UNI_PutX"
                => (UniMsg[q].Proc = Home /\ PendReqSrc = q))
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE,
                          !.Local = IF Dir.Local /\ ~Dir.Dirty THEN FALSE ELSE Dir.Local]
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, PendReqSrc, PendReqCmd, fwdVars>>

\* Stands in for NI_ShWb when the sharer is the abstract node: the writeback is
\* taken, but no sharer is recorded, the directory not tracking that node.
ABS_NI_ShWb ==
    /\ ShWbMsg.Cmd = "SHWB_ShWb" /\ ShWbMsg.Proc = Other
    /\ ShWbMsg' = [Cmd |-> "SHWB_None", Proc |-> Undefined, Data |-> Undefined]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.Dirty = FALSE, !.ShrVld = TRUE,
                          !.InvSet = Dir.ShrSet]
    /\ MemData' = ShWbMsg.Data
    /\ UNCHANGED <<Home, Proc, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars>>

-------------------------------------------------------------------------------

(* Abstract environment steps: the `Other`-node interactions summarised by the *)
(* ABS_* rules.                                                                *)
Environment ==
    \/ \E data \in DATA : ABS_Store(data)
    \/ \E src \in NODE :
         \/ ABS_NI_Remote_Nak_src(src)
         \/ ABS_NI_Remote_Get_Nak_dst(src)
         \/ ABS_NI_Remote_Get_Put_src(src)  \/ ABS_NI_Remote_Get_Put_dst(src)
         \/ ABS_NI_Remote_GetX_Nak_dst(src)
         \/ ABS_NI_Remote_GetX_PutX_src(src) \/ ABS_NI_Remote_GetX_PutX_dst(src)
    \/ ABS_PI_Remote_PutX
    \/ ABS_NI_Local_Get_Get \/ ABS_NI_Local_Get_Put
    \/ ABS_NI_Remote_Nak_src_dst \/ ABS_NI_Remote_Get_Put_src_dst
    \/ ABS_NI_Local_GetX_GetX \/ ABS_NI_Local_GetX_PutX
    \/ ABS_NI_Remote_GetX_PutX_src_dst
    \/ ABS_NI_InvAck \/ ABS_NI_ShWb

(* The protocol's next-state relation, less one step, plus the ABS_* rules.    *)
(* NI_ShWb records the sender of a shared writeback as a sharer, and here that *)
(* sender may be `Other`, which the directory does not track, so an NI_ShWb    *)
(* step on the abstract node's behalf is subtracted and ABS_NI_ShWb serves it. *)
CMPNext ==
    \/ Next /\ ~(ShWbMsg.Proc = Other /\ NI_ShWb)
    \/ Environment

CMPSpec == Init /\ [][CMPNext]_vars

THEOREM ABS_TypeCorrect == CMPSpec => []ABS_TypeOK

-------------------------------------------------------------------------------
(* Fairness.  The inherited groups are extended with the ABS_* rules that      *)
(* serve the same message slot, and the abstract node's replies to a forwarded *)
(* request get groups of their own: Home forwards to the abstract node and     *)
(* waits, so without fairness there the directory could stay pending forever.  *)
(* As in FlashWithMutex nothing constrains the voluntary actions, which here   *)
(* also covers the ABS_* rules by which the abstract node issues requests.     *)

ABS_HandleUni(n) ==
    \/ HandleUni(n)
    \/ ABS_NI_Remote_Get_Nak_dst(n)  \/ ABS_NI_Remote_GetX_Nak_dst(n)
    \/ ABS_NI_Remote_Get_Put_dst(n)  \/ ABS_NI_Remote_GetX_PutX_dst(n)

ABS_HandleShWb == HandleShWb \/ ABS_NI_ShWb

\* A request Home forwarded to node d on the abstract node's behalf: the reply
\* comes from the abstract node, so it has to be fair or the directory would
\* stay pending forever.
AbsRespond(d) ==
    \/ ABS_NI_Remote_Nak_src(d)
    \/ ABS_NI_Remote_Get_Put_src(d)
    \/ ABS_NI_Remote_GetX_PutX_src(d)

\* As AbsRespond, with the forwarding target abstract as well.
AbsRespondSrcDst ==
    \/ ABS_NI_Remote_Nak_src_dst
    \/ ABS_NI_Remote_Get_Put_src_dst
    \/ ABS_NI_Remote_GetX_PutX_src_dst

CMPFairness ==
    /\ \A n \in NODE : /\ WF_vars(ABS_HandleUni(n))
                       /\ WF_vars(HandleInv(n))
                       /\ WF_vars(NI_Replace(n))
                       /\ WF_vars(AbsRespond(n))
    /\ WF_vars(NI_Nak_Clear)
    /\ WF_vars(NI_Wb)
    /\ WF_vars(ABS_HandleShWb)
    /\ WF_vars(ABS_NI_InvAck)
    /\ WF_vars(AbsRespondSrcDst)

CMPFairSpec == Init /\ [][CMPNext]_vars /\ CMPFairness

-------------------------------------------------------------------------------
(* The properties are inherited verbatim: each quantifies over NODE, so under  *)
(* the abstraction each states that the concrete nodes make progress and stay  *)
(* coherent whatever the summarized ones do.                                   *)

THEOREM ABS_ReqProgressCorrect  == CMPFairSpec => ReqProgress
THEOREM ABS_DirProgressCorrect  == CMPFairSpec => DirProgress
THEOREM ABS_UniProgressCorrect  == CMPFairSpec => UniProgress
THEOREM ABS_InvProgressCorrect  == CMPFairSpec => InvProgress
THEOREM ABS_RpProgressCorrect   == CMPFairSpec => RpProgress
THEOREM ABS_WbProgressCorrect   == CMPFairSpec => WbProgress
THEOREM ABS_ShWbProgressCorrect == CMPFairSpec => ShWbProgress
THEOREM ABS_NakcProgressCorrect == CMPFairSpec => NakcProgress

THEOREM ABS_CacheStateCorrect == CMPSpec => []CacheStateProp
THEOREM ABS_CacheDataCorrect  == CMPSpec => []CacheDataProp
THEOREM ABS_MemDataCorrect    == CMPSpec => []MemDataProp

THEOREM ABS_Lemma_1_Correct == CMPSpec => []Lemma_1
THEOREM ABS_Lemma_2_Correct == CMPSpec => []Lemma_2
THEOREM ABS_Lemma_3_Correct == CMPSpec => []Lemma_3
THEOREM ABS_Lemma_4_Correct == CMPSpec => []Lemma_4
THEOREM ABS_Lemma_5_Correct == CMPSpec => []Lemma_5

===============================================================================
