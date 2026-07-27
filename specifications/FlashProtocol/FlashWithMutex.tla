------------------------------ MODULE FlashWithMutex ------------------------------
(***************************************************************************)
(* A faithful, one-action-per-rule (1:1) translation of                    *)
(* ProtocolDeadlockFiles/flashWithMutex.m (the FLASH directory-based cache  *)
(* coherence protocol with the CMP "Other"-node abstraction, Env_o = TRUE). *)
(*                                                                          *)
(* Structure mirrors the Murphi model exactly: every field of the Murphi    *)
(* record `Sta : STATE` is a top-level variable, next to the scalar         *)
(* Home.  Enum values use the identical Murphi spelling ("CACHE_I",         *)
(* "UNI_Get", ...) and variable and record field names are identical, so    *)
(* the equivalence mapping is tiny.                                         *)
(*                                                                          *)
(* The Murphi auxiliary ghost `LastOtherInvAck` is the only variable whose  *)
(* value depends on scalarset iteration order; it gates no transition and   *)
(* feeds no kept variable, so it is omitted here and projected away on the  *)
(* Murphi side by the comparator's ignorePaths.                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    NODE,        \* scalarset(NODE_NUM)   -- concrete nodes
    DATA,        \* scalarset(DATA_NUM)   -- data values
    Other,       \* the abstract CMP node (enum{Other})
    Undefined    \* the "undefine"/isundefined sentinel

ASSUME OtherNotInNODE   == Other \notin NODE
ASSUME UndefNotInNODE   == Undefined \notin NODE
ASSUME UndefNotInDATA   == Undefined \notin DATA
ASSUME UndefNotOther    == Undefined # Other
ASSUME NODENonEmpty     == NODE # {}
ASSUME DATANonEmpty     == DATA # {}
ASSUME NODEFinite       == IsFiniteSet(NODE)

ABS_NODE == NODE \cup {Other}

CACHE_STATE == {"CACHE_I", "CACHE_S", "CACHE_E"}
NODE_CMD    == {"NODE_None", "NODE_Get", "NODE_GetX"}
UNI_CMD     == {"UNI_None", "UNI_Get", "UNI_GetX", "UNI_Put", "UNI_PutX", "UNI_Nak"}
INV_CMD     == {"INV_None", "INV_Inv", "INV_InvAck"}
RP_CMD      == {"RP_None", "RP_Replace"}
WB_CMD      == {"WB_None", "WB_Wb"}
SHWB_CMD    == {"SHWB_None", "SHWB_ShWb", "SHWB_FAck"}
NAKC_CMD    == {"NAKC_None", "NAKC_Nakc"}
ReqCmd      == {"Get", "GetX"}   \* shared vs. exclusive request flavour

DataU  == DATA \cup {Undefined}
NodeU  == ABS_NODE \cup {Undefined}
UniU   == UNI_CMD \cup {Undefined}

VARIABLES
    Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
    CurrData, PrevData, PendReqSrc, PendReqCmd, Collecting, FwdCmd, FwdSrc, Env_o

vars == <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
          CurrData, PrevData, PendReqSrc, PendReqCmd, Collecting, FwdCmd, FwdSrc,
          Env_o>>

\* The history variables.  CurrData is the value most recently written:
\* the ABS_* actions hand it out as the abstract node's copy, and the data
\* properties check cached copies against it.  PrevData snapshots CurrData when
\* an invalidation round opens; nothing but CacheDataProp reads it, to let a
\* sharer still hold the pre-round value while Collecting.

\* Variables that most actions leave untouched as a unit, grouped so that the
\* frame conditions can name the group instead of listing its members.  An
\* action that does change one member spells the group's others out.

\* The request Home is currently working on, and whether it is still waiting
\* for invalidation acks.
pendVars == <<PendReqSrc, PendReqCmd, Collecting>>

\* The request Home forwarded to the dirty node.
fwdVars == <<FwdCmd, FwdSrc>>

-------------------------------------------------------------------------------

TypeOK ==
    /\ Home \in NODE
    /\ Proc \in [NODE -> [ProcCmd : NODE_CMD, InvMarked : BOOLEAN,
                          CacheState : CACHE_STATE, CacheData : DataU]]
    /\ Dir \in [Pending : BOOLEAN, Local : BOOLEAN, Dirty : BOOLEAN,
                HeadVld : BOOLEAN, HeadPtr : NodeU, ShrVld : BOOLEAN,
                ShrSet : SUBSET NODE, InvSet : SUBSET NODE]
    /\ MemData \in DATA
    /\ UniMsg \in [NODE -> [Cmd : UNI_CMD, Proc : NodeU, Data : DataU]]
    /\ InvMsg \in [NODE -> [Cmd : INV_CMD]]
    /\ RpMsg  \in [NODE -> [Cmd : RP_CMD]]
    /\ WbMsg   \in [Cmd : WB_CMD, Proc : NodeU, Data : DataU]
    /\ ShWbMsg \in [Cmd : SHWB_CMD, Proc : NodeU, Data : DataU]
    /\ NakcMsg \in [Cmd : NAKC_CMD]
    /\ CurrData \in DATA
    /\ PrevData \in DATA
    /\ PendReqSrc \in NodeU
    /\ PendReqCmd \in UniU
    /\ Collecting \in BOOLEAN
    /\ FwdCmd \in UNI_CMD
    /\ FwdSrc \in NodeU
    /\ Env_o \in BOOLEAN

-------------------------------------------------------------------------------

Init ==
    \E h \in NODE, d \in DATA :
        /\ Home = h
        /\ Proc = [i \in NODE |-> [ProcCmd |-> "NODE_None", InvMarked |-> FALSE,
                                   CacheState |-> "CACHE_I", CacheData |-> Undefined]]
        /\ Dir  = [Pending |-> FALSE, Local |-> FALSE, Dirty |-> FALSE,
                   HeadVld |-> FALSE, HeadPtr |-> Undefined, ShrVld |-> FALSE,
                   ShrSet |-> {}, InvSet |-> {}]
        /\ MemData = d
        /\ UniMsg  = [i \in NODE |-> [Cmd |-> "UNI_None", Proc |-> Undefined, Data |-> Undefined]]
        /\ InvMsg  = [i \in NODE |-> [Cmd |-> "INV_None"]]
        /\ RpMsg   = [i \in NODE |-> [Cmd |-> "RP_None"]]
        /\ WbMsg   = [Cmd |-> "WB_None", Proc |-> Undefined, Data |-> Undefined]
        /\ ShWbMsg = [Cmd |-> "SHWB_None", Proc |-> Undefined, Data |-> Undefined]
        /\ NakcMsg = [Cmd |-> "NAKC_None"]
        /\ CurrData = d
        /\ PrevData = d
        /\ PendReqSrc = Undefined
        /\ PendReqCmd = Undefined
        /\ Collecting = FALSE
        /\ FwdCmd = "UNI_None"
        /\ FwdSrc = Undefined
        /\ Env_o = TRUE

-------------------------------------------------------------------------------
(* Shared fragments of the *_GetX_PutX actions, which grant a line            *)
(* exclusively and so have to revoke it from everyone else first.             *)

\* The nodes that must be invalidated before the line can be granted: the
\* sharers and the head, less Home and the requester themselves.
InvNodes(exclude) ==
    {p \in NODE \ exclude : \/ (Dir.ShrVld /\ p \in Dir.ShrSet)
                            \/ (Dir.HeadVld /\ Dir.HeadPtr = p)}

\* Nobody has to be invalidated: either there is no head pointer, or req is
\* already the head and the only sharer.
NoOtherSharers(req) ==
    Dir.HeadVld => (Dir.HeadPtr = req /\ Dir.ShrSet \subseteq {req})

\* Home's line dropped, because the GetX takes it away.
ProcHomeInvalid ==
    [Proc EXCEPT ![Home].CacheState = "CACHE_I", ![Home].CacheData = Undefined]

\* As ProcHomeInvalid, but a Get of Home's that is still in flight is marked, so
\* that its reply is not mistaken for a fresh grant.
ProcHomeInvalidMarked ==
    [Proc EXCEPT ![Home].CacheState = "CACHE_I", ![Home].CacheData = Undefined,
                 ![Home].InvMarked = IF Proc[Home].ProcCmd = "NODE_Get"
                                     THEN TRUE ELSE Proc[Home].InvMarked]

-------------------------------------------------------------------------------
(*                        Concrete (non-ABS) rules                           *)
-------------------------------------------------------------------------------

Store(src, data) ==
    /\ Proc[src].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![src].CacheData = data]
    /\ CurrData' = data
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   PrevData, pendVars, fwdVars, Env_o>>

\* Shared/exclusive request from a remote processor (merges the former
\* PI_Remote_Get / PI_Remote_GetX).
PI_Remote(src, c) ==
    /\ src # Home
    /\ Proc[src].ProcCmd = "NODE_None"
    /\ Proc[src].CacheState = "CACHE_I"
    /\ Proc' = [Proc EXCEPT ![src].ProcCmd = IF c = "Get" THEN "NODE_Get" ELSE "NODE_GetX"]
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = IF c = "Get" THEN "UNI_Get" ELSE "UNI_GetX",
                                ![src].Proc = Home,
                                ![src].Data = Undefined]
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

PI_Local_Get_Get ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState = "CACHE_I"
    /\ ~Dir.Pending /\ Dir.Dirty
    /\ Proc' = [Proc EXCEPT ![Home].ProcCmd = "NODE_Get"]
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ UniMsg' = [UniMsg EXCEPT ![Home].Cmd = "UNI_Get", ![Home].Proc = Dir.HeadPtr,
                                ![Home].Data = Undefined]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_Get" ELSE FwdCmd
    /\ PendReqSrc' = Home
    /\ PendReqCmd' = "UNI_Get"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, FwdSrc, Env_o>>

PI_Local_Get_Put ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState = "CACHE_I"
    /\ ~Dir.Pending /\ ~Dir.Dirty
    /\ Dir' = [Dir EXCEPT !.Local = TRUE]
    /\ Proc' = [Proc EXCEPT ![Home].ProcCmd = "NODE_None",
                            ![Home].InvMarked = FALSE,
                            ![Home].CacheState = IF Proc[Home].InvMarked THEN "CACHE_I" ELSE "CACHE_S",
                            ![Home].CacheData = IF Proc[Home].InvMarked THEN Undefined ELSE MemData]
    /\ UNCHANGED <<Home, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

PI_Local_GetX_GetX ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState \in {"CACHE_I", "CACHE_S"}
    /\ ~Dir.Pending /\ Dir.Dirty
    /\ Proc' = [Proc EXCEPT ![Home].ProcCmd = "NODE_GetX"]
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ UniMsg' = [UniMsg EXCEPT ![Home].Cmd = "UNI_GetX", ![Home].Proc = Dir.HeadPtr,
                                ![Home].Data = Undefined]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_GetX" ELSE FwdCmd
    /\ PendReqSrc' = Home
    /\ PendReqCmd' = "UNI_GetX"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, FwdSrc, Env_o>>

\* The line is shared: the sharers and the head are invalidated first, so
\* Home's own request goes pending.
PI_Local_GetX_PutX_Inv ==
    /\ Dir.HeadVld
    /\ Dir' = [Dir EXCEPT !.Local = TRUE, !.Dirty = TRUE, !.Pending = TRUE,
                          !.HeadVld = FALSE, !.HeadPtr = Undefined, !.ShrVld = FALSE,
                          !.ShrSet = {}, !.InvSet = InvNodes({Home})]
    /\ InvMsg' = [p \in NODE |-> [Cmd |-> IF p \in InvNodes({Home})
                                          THEN "INV_Inv" ELSE "INV_None"]]
    /\ PendReqSrc' = Home
    /\ Collecting' = TRUE
    /\ PrevData' = CurrData

\* Nobody holds the line, so it is granted right away.
PI_Local_GetX_PutX_Grant ==
    /\ ~Dir.HeadVld
    /\ Dir' = [Dir EXCEPT !.Local = TRUE, !.Dirty = TRUE]
    /\ UNCHANGED <<InvMsg, PrevData, PendReqSrc, Collecting>>

PI_Local_GetX_PutX ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState \in {"CACHE_I", "CACHE_S"}
    /\ ~Dir.Pending /\ ~Dir.Dirty
    /\ Proc' = [Proc EXCEPT ![Home].ProcCmd = "NODE_None",
                            ![Home].InvMarked = FALSE,
                            ![Home].CacheState = "CACHE_E",
                            ![Home].CacheData = MemData]
    /\ \/ PI_Local_GetX_PutX_Inv
       \/ PI_Local_GetX_PutX_Grant
    /\ UNCHANGED <<Home, MemData, UniMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PendReqCmd, fwdVars, Env_o>>

PI_Remote_PutX(dst) ==
    /\ dst # Home
    /\ Proc[dst].ProcCmd = "NODE_None"
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_I", ![dst].CacheData = Undefined]
    /\ WbMsg' = [WbMsg EXCEPT !.Cmd = "WB_Wb", !.Proc = dst, !.Data = Proc[dst].CacheData]
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, RpMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

PI_Local_PutX ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![Home].CacheState = "CACHE_I", ![Home].CacheData = Undefined]
    /\ Dir' = [Dir EXCEPT !.Dirty = FALSE, !.Local = IF Dir.Pending THEN Dir.Local ELSE FALSE]
    /\ MemData' = Proc[Home].CacheData
    /\ UNCHANGED <<Home, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars, Env_o>>

PI_Remote_Replace(src) ==
    /\ src # Home
    /\ Proc[src].ProcCmd = "NODE_None"
    /\ Proc[src].CacheState = "CACHE_S"
    /\ Proc' = [Proc EXCEPT ![src].CacheState = "CACHE_I", ![src].CacheData = Undefined]
    /\ RpMsg' = [RpMsg EXCEPT ![src].Cmd = "RP_Replace"]
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

PI_Local_Replace ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState = "CACHE_S"
    /\ Dir' = [Dir EXCEPT !.Local = FALSE]
    /\ Proc' = [Proc EXCEPT ![Home].CacheState = "CACHE_I", ![Home].CacheData = Undefined]
    /\ UNCHANGED <<Home, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

NI_Nak(dst) ==
    /\ UniMsg[dst].Cmd = "UNI_Nak"
    /\ UniMsg' = [UniMsg EXCEPT ![dst].Cmd = "UNI_None", ![dst].Proc = Undefined, ![dst].Data = Undefined]
    /\ Proc' = [Proc EXCEPT ![dst].ProcCmd = "NODE_None", ![dst].InvMarked = FALSE]
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

NI_Nak_Clear ==
    /\ NakcMsg.Cmd = "NAKC_Nakc"
    /\ NakcMsg' = [NakcMsg EXCEPT !.Cmd = "NAKC_None"]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE]
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

NI_Local_Get_Nak(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_Get"
    /\ UniMsg[src].Proc = Home
    /\ RpMsg[src].Cmd # "RP_Replace"
    /\ \/ Dir.Pending
       \/ (Dir.Dirty /\ Dir.Local /\ Proc[Home].CacheState # "CACHE_E")
       \/ (Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr = src)
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_Nak", ![src].Proc = Home, ![src].Data = Undefined]
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

NI_Local_Get_Get(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_Get"
    /\ UniMsg[src].Proc = Home
    /\ RpMsg[src].Cmd # "RP_Replace"
    /\ ~Dir.Pending /\ Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr # src
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_Get", ![src].Proc = Dir.HeadPtr, ![src].Data = Undefined]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_Get" ELSE FwdCmd
    /\ PendReqSrc' = src
    /\ PendReqCmd' = "UNI_Get"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, Proc, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, FwdSrc, Env_o>>

NI_Local_Get_Put(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_Get"
    /\ UniMsg[src].Proc = Home
    /\ RpMsg[src].Cmd # "RP_Replace"
    /\ ~Dir.Pending
    /\ (Dir.Dirty => (Dir.Local /\ Proc[Home].CacheState = "CACHE_E"))
    /\ Dir' = IF Dir.Dirty
              THEN [Dir EXCEPT !.Dirty = FALSE, !.HeadVld = TRUE, !.HeadPtr = src]
              ELSE IF Dir.HeadVld
                   THEN [Dir EXCEPT !.ShrVld = TRUE, !.ShrSet = Dir.ShrSet \cup {src},
                                    !.InvSet = Dir.ShrSet \cup {src}]
                   ELSE [Dir EXCEPT !.HeadVld = TRUE, !.HeadPtr = src]
    /\ MemData' = IF Dir.Dirty THEN Proc[Home].CacheData ELSE MemData
    /\ Proc' = IF Dir.Dirty THEN [Proc EXCEPT ![Home].CacheState = "CACHE_S"] ELSE Proc
    /\ UniMsg' = IF Dir.Dirty
                 THEN [UniMsg EXCEPT ![src].Cmd = "UNI_Put", ![src].Proc = Home,
                                     ![src].Data = Proc[Home].CacheData]
                 ELSE [UniMsg EXCEPT ![src].Cmd = "UNI_Put", ![src].Proc = Home,
                                     ![src].Data = MemData]
    /\ UNCHANGED <<Home, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData, PrevData,
                   pendVars, fwdVars, Env_o>>

\* Remote NAK of a shared/exclusive request (merges the former
\* NI_Remote_Get_Nak / NI_Remote_GetX_Nak).
NI_Remote_Nak(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ UniMsg[src].Cmd \in {"UNI_Get", "UNI_GetX"}
    /\ UniMsg[src].Proc = dst
    /\ Proc[dst].CacheState # "CACHE_E"
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_Nak", ![src].Proc = dst, ![src].Data = Undefined]
    /\ NakcMsg' = [NakcMsg EXCEPT !.Cmd = "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, CurrData,
                   PrevData, pendVars, Env_o>>

NI_Remote_Get_Put(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ UniMsg[src].Cmd = "UNI_Get"
    /\ UniMsg[src].Proc = dst
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_S"]
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_Put", ![src].Proc = dst,
                                ![src].Data = Proc[dst].CacheData]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ ShWbMsg' = IF src # Home
                  THEN [ShWbMsg EXCEPT !.Cmd = "SHWB_ShWb", !.Proc = src, !.Data = Proc[dst].CacheData]
                  ELSE ShWbMsg
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, Env_o>>

NI_Local_GetX_Nak(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_GetX"
    /\ UniMsg[src].Proc = Home
    /\ \/ Dir.Pending
       \/ (Dir.Dirty /\ Dir.Local /\ Proc[Home].CacheState # "CACHE_E")
       \/ (Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr = src)
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_Nak", ![src].Proc = Home, ![src].Data = Undefined]
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

NI_Local_GetX_GetX(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_GetX"
    /\ UniMsg[src].Proc = Home
    /\ ~Dir.Pending /\ Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr # src
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_GetX", ![src].Proc = Dir.HeadPtr, ![src].Data = Undefined]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_GetX" ELSE FwdCmd
    /\ PendReqSrc' = src
    /\ PendReqCmd' = "UNI_GetX"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, Proc, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, FwdSrc, Env_o>>

\* Home holds the line exclusively, so it can be handed to src directly.
NI_Local_GetX_PutX_Dirty(src) ==
    /\ Dir.Dirty
    /\ Dir' = [Dir EXCEPT !.Local = FALSE, !.Dirty = TRUE, !.HeadVld = TRUE,
                          !.HeadPtr = src, !.ShrVld = FALSE, !.ShrSet = {}, !.InvSet = {}]
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_PutX", ![src].Proc = Home,
                                ![src].Data = Proc[Home].CacheData]
    /\ Proc' = ProcHomeInvalid
    /\ UNCHANGED <<InvMsg, PrevData, pendVars>>

\* src is already the head and the only sharer, so nobody has to be invalidated
\* and memory's copy is handed over.
NI_Local_GetX_PutX_Grant(src) ==
    /\ ~Dir.Dirty
    /\ NoOtherSharers(src)
    /\ Dir' = [Dir EXCEPT !.Local = FALSE, !.Dirty = TRUE, !.HeadVld = TRUE,
                          !.HeadPtr = src, !.ShrVld = FALSE, !.ShrSet = {}, !.InvSet = {}]
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_PutX", ![src].Proc = Home,
                                ![src].Data = MemData]
    /\ Proc' = IF Dir.Local THEN ProcHomeInvalidMarked ELSE ProcHomeInvalid
    /\ UNCHANGED <<InvMsg, PrevData, pendVars>>

\* Others share the line: they are invalidated first and the request goes
\* pending until their acks come back.
NI_Local_GetX_PutX_Inv(src) ==
    /\ ~Dir.Dirty
    /\ ~NoOtherSharers(src)
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE, !.Local = FALSE, !.Dirty = TRUE,
                          !.HeadVld = TRUE, !.HeadPtr = src, !.ShrVld = FALSE,
                          !.ShrSet = {}, !.InvSet = InvNodes({Home, src})]
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_PutX", ![src].Proc = Home,
                                ![src].Data = MemData]
    /\ Proc' = IF Dir.Local THEN ProcHomeInvalidMarked ELSE Proc
    /\ InvMsg' = [p \in NODE |-> [Cmd |-> IF p \in InvNodes({Home, src})
                                          THEN "INV_Inv" ELSE "INV_None"]]
    /\ PendReqSrc' = src
    /\ PendReqCmd' = "UNI_GetX"
    /\ Collecting' = TRUE
    /\ PrevData' = CurrData

NI_Local_GetX_PutX(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_GetX"
    /\ UniMsg[src].Proc = Home
    /\ ~Dir.Pending
    /\ (Dir.Dirty => (Dir.Local /\ Proc[Home].CacheState = "CACHE_E"))
    /\ \/ NI_Local_GetX_PutX_Dirty(src)
       \/ NI_Local_GetX_PutX_Grant(src)
       \/ NI_Local_GetX_PutX_Inv(src)
    /\ UNCHANGED <<Home, MemData, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData, fwdVars,
                   Env_o>>

NI_Remote_GetX_PutX(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ UniMsg[src].Cmd = "UNI_GetX"
    /\ UniMsg[src].Proc = dst
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_I", ![dst].CacheData = Undefined]
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_PutX", ![src].Proc = dst,
                                ![src].Data = Proc[dst].CacheData]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ ShWbMsg' = IF src # Home
                  THEN [ShWbMsg EXCEPT !.Cmd = "SHWB_FAck", !.Proc = src, !.Data = Undefined]
                  ELSE ShWbMsg
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, Env_o>>

NI_Local_Put ==
    /\ UniMsg[Home].Cmd = "UNI_Put"
    /\ UniMsg' = [UniMsg EXCEPT ![Home].Cmd = "UNI_None", ![Home].Proc = Undefined, ![Home].Data = Undefined]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.Dirty = FALSE, !.Local = TRUE]
    /\ MemData' = UniMsg[Home].Data
    /\ Proc' = [Proc EXCEPT ![Home].ProcCmd = "NODE_None",
                            ![Home].InvMarked = FALSE,
                            ![Home].CacheState = IF Proc[Home].InvMarked THEN "CACHE_I" ELSE "CACHE_S",
                            ![Home].CacheData = IF Proc[Home].InvMarked THEN Undefined ELSE UniMsg[Home].Data]
    /\ UNCHANGED <<Home, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData, PrevData,
                   pendVars, fwdVars, Env_o>>

NI_Remote_Put(dst) ==
    /\ dst # Home
    /\ UniMsg[dst].Cmd = "UNI_Put"
    /\ UniMsg' = [UniMsg EXCEPT ![dst].Cmd = "UNI_None", ![dst].Proc = Undefined, ![dst].Data = Undefined]
    /\ Proc' = [Proc EXCEPT ![dst].ProcCmd = "NODE_None",
                            ![dst].InvMarked = FALSE,
                            ![dst].CacheState = IF Proc[dst].InvMarked THEN "CACHE_I" ELSE "CACHE_S",
                            ![dst].CacheData = IF Proc[dst].InvMarked THEN Undefined ELSE UniMsg[dst].Data]
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

NI_Local_PutXAcksDone ==
    /\ UniMsg[Home].Cmd = "UNI_PutX"
    /\ UniMsg' = [UniMsg EXCEPT ![Home].Cmd = "UNI_None", ![Home].Proc = Undefined, ![Home].Data = Undefined]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.Local = TRUE, !.HeadVld = FALSE, !.HeadPtr = Undefined]
    /\ Proc' = [Proc EXCEPT ![Home].ProcCmd = "NODE_None",
                            ![Home].InvMarked = FALSE,
                            ![Home].CacheState = "CACHE_E",
                            ![Home].CacheData = UniMsg[Home].Data]
    /\ UNCHANGED <<Home, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars, Env_o>>

NI_Remote_PutX(dst) ==
    /\ dst # Home
    /\ UniMsg[dst].Cmd = "UNI_PutX"
    /\ Proc[dst].ProcCmd = "NODE_GetX"
    /\ UniMsg' = [UniMsg EXCEPT ![dst].Cmd = "UNI_None", ![dst].Proc = Undefined, ![dst].Data = Undefined]
    /\ Proc' = [Proc EXCEPT ![dst].ProcCmd = "NODE_None",
                            ![dst].InvMarked = FALSE,
                            ![dst].CacheState = "CACHE_E",
                            ![dst].CacheData = UniMsg[dst].Data]
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

NI_Inv(dst) ==
    /\ dst # Home
    /\ InvMsg[dst].Cmd = "INV_Inv"
    /\ InvMsg' = [InvMsg EXCEPT ![dst].Cmd = "INV_InvAck"]
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_I",
                            ![dst].CacheData = Undefined,
                            ![dst].InvMarked = IF Proc[dst].ProcCmd = "NODE_Get" THEN TRUE
                                               ELSE Proc[dst].InvMarked]
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

\* Acks are still outstanding: only this one is recorded.
NI_InvAck_More(src) ==
    /\ Dir.InvSet \ {src} # {}
    /\ Dir' = [Dir EXCEPT !.InvSet = Dir.InvSet \ {src}]
    /\ UNCHANGED Collecting

\* The last ack: the invalidation round is complete and the request retires.
NI_InvAck_Last(src) ==
    /\ Dir.InvSet \ {src} = {}
    /\ Dir' = [Dir EXCEPT !.InvSet = Dir.InvSet \ {src}, !.Pending = FALSE,
                          !.Local = IF Dir.Local /\ ~Dir.Dirty THEN FALSE ELSE Dir.Local]
    /\ Collecting' = FALSE

NI_InvAck(src) ==
    /\ src # Home
    /\ InvMsg[src].Cmd = "INV_InvAck"
    /\ Dir.Pending /\ src \in Dir.InvSet
    /\ InvMsg' = [InvMsg EXCEPT ![src].Cmd = "INV_None"]
    /\ \/ NI_InvAck_More(src)
       \/ NI_InvAck_Last(src)
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, PendReqSrc, PendReqCmd, fwdVars, Env_o>>

NI_Wb ==
    /\ WbMsg.Cmd = "WB_Wb"
    /\ WbMsg' = [WbMsg EXCEPT !.Cmd = "WB_None", !.Proc = Undefined, !.Data = Undefined]
    /\ Dir' = [Dir EXCEPT !.Dirty = FALSE, !.HeadVld = FALSE, !.HeadPtr = Undefined]
    /\ MemData' = WbMsg.Data
    /\ UNCHANGED <<Home, Proc, UniMsg, InvMsg, RpMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars, Env_o>>

NI_FAck ==
    /\ ShWbMsg.Cmd = "SHWB_FAck"
    /\ ShWbMsg' = [ShWbMsg EXCEPT !.Cmd = "SHWB_None", !.Proc = Undefined, !.Data = Undefined]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.HeadPtr = IF Dir.Dirty THEN ShWbMsg.Proc ELSE Dir.HeadPtr]
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

NI_ShWb ==
    /\ ShWbMsg.Cmd = "SHWB_ShWb"
    /\ ShWbMsg' = [ShWbMsg EXCEPT !.Cmd = "SHWB_None", !.Proc = Undefined, !.Data = Undefined]
    \* ShWbMsg.Proc is Other when the sharer is the abstract node; only concrete
    \* nodes are recorded in the directory.
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.Dirty = FALSE, !.ShrVld = TRUE,
                          !.ShrSet = Dir.ShrSet \cup ({ShWbMsg.Proc} \cap NODE),
                          !.InvSet = Dir.ShrSet \cup ({ShWbMsg.Proc} \cap NODE)]
    /\ MemData' = ShWbMsg.Data
    /\ UNCHANGED <<Home, Proc, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars, Env_o>>

NI_Replace(src) ==
    /\ RpMsg[src].Cmd = "RP_Replace"
    /\ RpMsg' = [RpMsg EXCEPT ![src].Cmd = "RP_None"]
    /\ Dir' = [Dir EXCEPT !.ShrSet = IF Dir.ShrVld THEN Dir.ShrSet \ {src} ELSE Dir.ShrSet,
                          !.InvSet = IF Dir.ShrVld THEN Dir.InvSet \ {src} ELSE Dir.InvSet]
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

-------------------------------------------------------------------------------
(*                    ABS_* abstract-environment rules                       *)
-------------------------------------------------------------------------------
(* Shared guard fragment used by the ABS_* environment rules that summarize  *)
(* a writeback from the abstract node (Lemma_1 side condition).              *)

AbsDirtyClean ==
    /\ Dir.Dirty
    /\ WbMsg.Cmd # "WB_Wb"
    /\ ShWbMsg.Cmd # "SHWB_ShWb"
    /\ \A p \in NODE : Proc[p].CacheState # "CACHE_E"
    /\ UniMsg[Home].Cmd # "UNI_Put"
    /\ \A q \in NODE : UniMsg[q].Cmd # "UNI_PutX"

ABS_Store(data) ==
    /\ Env_o
    /\ AbsDirtyClean
    /\ CurrData' = data
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg,
                   NakcMsg, PrevData, pendVars, fwdVars, Env_o>>

ABS_PI_Remote_PutX ==
    /\ Env_o
    /\ AbsDirtyClean
    /\ WbMsg' = [WbMsg EXCEPT !.Cmd = "WB_Wb", !.Proc = Other, !.Data = CurrData]
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars, Env_o>>

ABS_NI_Local_Get_Get ==
    /\ Env_o
    /\ ~Dir.Pending /\ Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr # Other
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_Get" ELSE FwdCmd
    /\ PendReqSrc' = Other
    /\ PendReqCmd' = "UNI_Get"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, FwdSrc, Env_o>>

ABS_NI_Local_Get_Put ==
    /\ Env_o
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
                   PrevData, pendVars, fwdVars, Env_o>>

\* Abstract remote NAK, source side (merges the former ABS_NI_Remote_Get_Nak_src
\* / ABS_NI_Remote_GetX_Nak_src).
ABS_NI_Remote_Nak_src(dst) ==
    /\ Env_o /\ dst # Home
    /\ Proc[dst].CacheState # "CACHE_E"
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd \in {"UNI_Get", "UNI_GetX"}
    /\ NakcMsg' = [NakcMsg EXCEPT !.Cmd = "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg,
                   CurrData, PrevData, pendVars, Env_o>>

ABS_NI_Remote_Get_Nak_dst(src) ==
    /\ Env_o
    /\ UniMsg[src].Cmd = "UNI_Get" /\ UniMsg[src].Proc = Other
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = src /\ FwdCmd = "UNI_Get"
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_Nak", ![src].Proc = Other, ![src].Data = Undefined]
    /\ NakcMsg' = [NakcMsg EXCEPT !.Cmd = "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, CurrData,
                   PrevData, pendVars, Env_o>>

\* Abstract remote NAK, both sides abstract (merges the former
\* ABS_NI_Remote_Get_Nak_src_dst / ABS_NI_Remote_GetX_Nak_src_dst).
ABS_NI_Remote_Nak_src_dst ==
    /\ Env_o
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd \in {"UNI_Get", "UNI_GetX"}
    /\ NakcMsg' = [NakcMsg EXCEPT !.Cmd = "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg,
                   CurrData, PrevData, pendVars, Env_o>>

ABS_NI_Remote_Get_Put_src(dst) ==
    /\ Env_o /\ dst # Home
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd = "UNI_Get"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_S"]
    /\ ShWbMsg' = [ShWbMsg EXCEPT !.Cmd = "SHWB_ShWb", !.Proc = Other, !.Data = Proc[dst].CacheData]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, Env_o>>

ABS_NI_Remote_Get_Put_dst(src) ==
    /\ Env_o
    /\ UniMsg[src].Cmd = "UNI_Get" /\ UniMsg[src].Proc = Other
    /\ AbsDirtyClean
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = src /\ FwdCmd = "UNI_Get"
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_Put", ![src].Proc = Other, ![src].Data = CurrData]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ ShWbMsg' = IF src # Home
                  THEN [ShWbMsg EXCEPT !.Cmd = "SHWB_ShWb", !.Proc = src, !.Data = CurrData]
                  ELSE ShWbMsg
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, Env_o>>

ABS_NI_Remote_Get_Put_src_dst ==
    /\ Env_o
    /\ AbsDirtyClean
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd = "UNI_Get"
    /\ ShWbMsg' = [ShWbMsg EXCEPT !.Cmd = "SHWB_ShWb", !.Proc = Other, !.Data = CurrData]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, Env_o>>

ABS_NI_Local_GetX_GetX ==
    /\ Env_o
    /\ ~Dir.Pending /\ Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr # Other
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_GetX" ELSE FwdCmd
    /\ PendReqSrc' = Other
    /\ PendReqCmd' = "UNI_GetX"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, FwdSrc, Env_o>>

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
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE, !.Local = FALSE, !.Dirty = TRUE,
                          !.HeadVld = TRUE, !.HeadPtr = Other, !.ShrVld = FALSE,
                          !.ShrSet = {}, !.InvSet = InvNodes({Home})]
    /\ Proc' = IF Dir.Local THEN ProcHomeInvalidMarked ELSE Proc
    /\ InvMsg' = [p \in NODE |-> [Cmd |-> IF p \in InvNodes({Home})
                                          THEN "INV_Inv" ELSE "INV_None"]]
    /\ PendReqSrc' = Other
    /\ PendReqCmd' = "UNI_GetX"
    /\ Collecting' = TRUE
    /\ PrevData' = CurrData

ABS_NI_Local_GetX_PutX ==
    /\ Env_o
    /\ ~Dir.Pending
    /\ (Dir.Dirty => (Dir.Local /\ Proc[Home].CacheState = "CACHE_E"))
    /\ \/ ABS_NI_Local_GetX_PutX_Dirty
       \/ ABS_NI_Local_GetX_PutX_Grant
       \/ ABS_NI_Local_GetX_PutX_Inv
    /\ UNCHANGED <<Home, MemData, UniMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   fwdVars, Env_o>>

ABS_NI_Remote_GetX_Nak_dst(src) ==
    /\ Env_o
    /\ UniMsg[src].Cmd = "UNI_GetX" /\ UniMsg[src].Proc = Other
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = src /\ FwdCmd = "UNI_GetX"
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_Nak", ![src].Proc = Other, ![src].Data = Undefined]
    /\ NakcMsg' = [NakcMsg EXCEPT !.Cmd = "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, CurrData,
                   PrevData, pendVars, Env_o>>

ABS_NI_Remote_GetX_PutX_src(dst) ==
    /\ Env_o /\ dst # Home
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd = "UNI_GetX"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_I", ![dst].CacheData = Undefined]
    /\ ShWbMsg' = [ShWbMsg EXCEPT !.Cmd = "SHWB_FAck", !.Proc = Other, !.Data = Undefined]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, Env_o>>

ABS_NI_Remote_GetX_PutX_dst(src) ==
    /\ Env_o
    /\ UniMsg[src].Cmd = "UNI_GetX" /\ UniMsg[src].Proc = Other
    /\ AbsDirtyClean
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = src /\ FwdCmd = "UNI_GetX"
    /\ UniMsg' = [UniMsg EXCEPT ![src].Cmd = "UNI_PutX", ![src].Proc = Other, ![src].Data = CurrData]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ ShWbMsg' = IF src # Home
                  THEN [ShWbMsg EXCEPT !.Cmd = "SHWB_FAck", !.Proc = src, !.Data = Undefined]
                  ELSE ShWbMsg
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, Env_o>>

ABS_NI_Remote_GetX_PutX_src_dst ==
    /\ Env_o
    /\ AbsDirtyClean
    /\ Dir.Pending /\ ~Dir.Local
    /\ PendReqSrc = Other /\ FwdCmd = "UNI_GetX"
    /\ ShWbMsg' = [ShWbMsg EXCEPT !.Cmd = "SHWB_FAck", !.Proc = Other, !.Data = Undefined]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = Other
    /\ UNCHANGED <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, Env_o>>

\* All concrete nodes have acked: the round closes and the request retires.
\* The Murphi rule also fires while acks are still outstanding, but that branch
\* assigns nothing except the dropped ghosts LastInvAck and LastOtherInvAck, so
\* here it would be a stuttering step and is left out.
ABS_NI_InvAck ==
    /\ Env_o
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
                   CurrData, PrevData, PendReqSrc, PendReqCmd, fwdVars, Env_o>>

ABS_NI_ShWb ==
    /\ Env_o
    /\ ShWbMsg.Cmd = "SHWB_ShWb" /\ ShWbMsg.Proc = Other
    /\ ShWbMsg' = [ShWbMsg EXCEPT !.Cmd = "SHWB_None", !.Proc = Undefined, !.Data = Undefined]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.Dirty = FALSE, !.ShrVld = TRUE,
                          !.InvSet = Dir.ShrSet]
    /\ MemData' = ShWbMsg.Data
    /\ UNCHANGED <<Home, Proc, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars, Env_o>>

-------------------------------------------------------------------------------

(* Concrete protocol steps (the modelled nodes and directory). *)
System ==
    \/ \E src \in NODE, data \in DATA : Store(src, data)
    \/ \E src \in NODE :
         \/ \E c \in ReqCmd : PI_Remote(src, c)
         \/ PI_Remote_Replace(src)
         \/ NI_Local_Get_Nak(src) \/ NI_Local_Get_Get(src) \/ NI_Local_Get_Put(src)
         \/ NI_Local_GetX_Nak(src) \/ NI_Local_GetX_GetX(src) \/ NI_Local_GetX_PutX(src)
         \/ NI_InvAck(src) \/ NI_Replace(src)
    \/ \E dst \in NODE :
         \/ PI_Remote_PutX(dst)
         \/ NI_Nak(dst) \/ NI_Remote_Put(dst) \/ NI_Remote_PutX(dst) \/ NI_Inv(dst)
    \/ \E src \in NODE, dst \in NODE :
         \/ NI_Remote_Nak(src, dst) \/ NI_Remote_Get_Put(src, dst)
         \/ NI_Remote_GetX_PutX(src, dst)
    \/ PI_Local_Get_Get \/ PI_Local_Get_Put
    \/ PI_Local_GetX_GetX \/ PI_Local_GetX_PutX
    \/ PI_Local_PutX \/ PI_Local_Replace
    \/ NI_Nak_Clear \/ NI_Local_Put \/ NI_Local_PutXAcksDone
    \/ NI_Wb \/ NI_FAck \/ NI_ShWb

(* Abstract environment steps: the CMP `Other`-node interactions summarised    *)
(* by the ABS_* rules (all guarded by Env_o).                                  *)
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

Next == System \/ Environment

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
(* Safety properties translated from the Murphi `invariant`s (for indep.     *)
(* cross-checking; not part of the bisimulation).                            *)

CacheStateProp ==
    \A p, q \in NODE :
        p # q => ~(Proc[p].CacheState = "CACHE_E" /\ Proc[q].CacheState = "CACHE_E")

CacheDataProp ==
    \A p \in NODE :
        /\ (Proc[p].CacheState = "CACHE_E" => Proc[p].CacheData = CurrData)
        /\ (Proc[p].CacheState = "CACHE_S" =>
              /\ (Collecting => Proc[p].CacheData = PrevData)
              /\ (~Collecting => Proc[p].CacheData = CurrData))

MemDataProp ==
    ~Dir.Dirty => MemData = CurrData
=============================================================================
