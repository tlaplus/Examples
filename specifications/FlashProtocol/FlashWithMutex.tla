------------------------------ MODULE FlashWithMutex ------------------------------
(*********************************************************************************)
(* The FLASH directory-based cache coherence protocol                            *)
(*                                                                               *)
(* Derived from a one-action-per-rule translation of                             *)
(* https://github.com/dsethi/ProtocolDeadlockFiles/blob/master/flashWithMutex.m  *)
(*                                                                               *)
(* FlashWithMutexCMP extends this module with the flashWithMutex.m model's CMP   *)
(* encoding, which keeps NODE concrete, but additionally encodes the set of all  *)
(* other nodes by more non-deterministic actions.  Note that there is no         *)
(* guarantee that the CMP encoding is sound.                                     *)
(*********************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    NODE,        \* scalarset(NODE_NUM)   -- the nodes
    DATA,        \* scalarset(DATA_NUM)   -- data values
    Undefined    \* the "undefine"/isundefined sentinel

ASSUME UndefNotInNODE   == Undefined \notin NODE
ASSUME UndefNotInDATA   == Undefined \notin DATA
ASSUME NODEDATADisjoint == NODE \cap DATA = {}
ASSUME NODENonEmpty     == NODE # {}
ASSUME DATANonEmpty     == DATA # {}
ASSUME NODEFinite       == IsFiniteSet(NODE)

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
NodeU  == NODE \cup {Undefined}
UniU   == UNI_CMD \cup {Undefined}

VARIABLES
    Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
    CurrData, PrevData, PendReqSrc, PendReqCmd, Collecting, FwdCmd, FwdSrc

vars == <<Home, Proc, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
          CurrData, PrevData, PendReqSrc, PendReqCmd, Collecting, FwdCmd, FwdSrc>>

\* The history variables.  CurrData is the value most recently written, which
\* the data properties check cached copies against.  PrevData snapshots
\* CurrData when an invalidation round opens; nothing but CacheDataProp reads
\* it, to let a sharer still hold the pre-round value while Collecting.

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
(*                            Protocol rules                                 *)
-------------------------------------------------------------------------------

Store(src, data) ==
    /\ Proc[src].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![src].CacheData = data]
    /\ CurrData' = data
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   PrevData, pendVars, fwdVars>>

\* Shared/exclusive request from a remote processor (merges the former
\* PI_Remote_Get / PI_Remote_GetX).
PI_Remote(src, c) ==
    /\ src # Home
    /\ Proc[src].ProcCmd = "NODE_None"
    /\ Proc[src].CacheState = "CACHE_I"
    /\ Proc' = [Proc EXCEPT ![src].ProcCmd = IF c = "Get" THEN "NODE_Get" ELSE "NODE_GetX"]
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> IF c = "Get" THEN "UNI_Get" ELSE "UNI_GetX",
                                          Proc |-> Home, Data |-> Undefined]]
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

PI_Local_Get_Get ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState = "CACHE_I"
    /\ ~Dir.Pending /\ Dir.Dirty
    /\ Proc' = [Proc EXCEPT ![Home].ProcCmd = "NODE_Get"]
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ UniMsg' = [UniMsg EXCEPT ![Home] = [Cmd |-> "UNI_Get", Proc |-> Dir.HeadPtr,
                                           Data |-> Undefined]]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_Get" ELSE FwdCmd
    /\ PendReqSrc' = Home
    /\ PendReqCmd' = "UNI_Get"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, FwdSrc>>

PI_Local_Get_Put ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState = "CACHE_I"
    /\ ~Dir.Pending /\ ~Dir.Dirty
    /\ Dir' = [Dir EXCEPT !.Local = TRUE]
    /\ Proc' = [Proc EXCEPT ![Home] = [ProcCmd |-> "NODE_None", InvMarked |-> FALSE,
                                       CacheState |-> IF Proc[Home].InvMarked THEN "CACHE_I" ELSE "CACHE_S",
                                       CacheData |-> IF Proc[Home].InvMarked THEN Undefined ELSE MemData]]
    /\ UNCHANGED <<Home, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

PI_Local_GetX_GetX ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState \in {"CACHE_I", "CACHE_S"}
    /\ ~Dir.Pending /\ Dir.Dirty
    /\ Proc' = [Proc EXCEPT ![Home].ProcCmd = "NODE_GetX"]
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ UniMsg' = [UniMsg EXCEPT ![Home] = [Cmd |-> "UNI_GetX", Proc |-> Dir.HeadPtr,
                                           Data |-> Undefined]]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_GetX" ELSE FwdCmd
    /\ PendReqSrc' = Home
    /\ PendReqCmd' = "UNI_GetX"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, FwdSrc>>

\* The line is shared: the sharers and the head are invalidated first, so
\* Home's own request goes pending.
PI_Local_GetX_PutX_Inv ==
    /\ Dir.HeadVld
    /\ Dir' = [Pending |-> TRUE, Local |-> TRUE, Dirty |-> TRUE, HeadVld |-> FALSE,
               HeadPtr |-> Undefined, ShrVld |-> FALSE, ShrSet |-> {}, InvSet |-> InvNodes({Home})]
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
    /\ Proc' = [Proc EXCEPT ![Home] = [ProcCmd |-> "NODE_None", InvMarked |-> FALSE,
                                       CacheState |-> "CACHE_E", CacheData |-> MemData]]
    /\ \/ PI_Local_GetX_PutX_Inv
       \/ PI_Local_GetX_PutX_Grant
    /\ UNCHANGED <<Home, MemData, UniMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PendReqCmd, fwdVars>>

PI_Remote_PutX(dst) ==
    /\ dst # Home
    /\ Proc[dst].ProcCmd = "NODE_None"
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_I", ![dst].CacheData = Undefined]
    /\ WbMsg' = [Cmd |-> "WB_Wb", Proc |-> dst, Data |-> Proc[dst].CacheData]
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, RpMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

PI_Local_PutX ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![Home].CacheState = "CACHE_I", ![Home].CacheData = Undefined]
    /\ Dir' = [Dir EXCEPT !.Dirty = FALSE, !.Local = IF Dir.Pending THEN Dir.Local ELSE FALSE]
    /\ MemData' = Proc[Home].CacheData
    /\ UNCHANGED <<Home, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars>>

PI_Remote_Replace(src) ==
    /\ src # Home
    /\ Proc[src].ProcCmd = "NODE_None"
    /\ Proc[src].CacheState = "CACHE_S"
    /\ Proc' = [Proc EXCEPT ![src].CacheState = "CACHE_I", ![src].CacheData = Undefined]
    /\ RpMsg' = [RpMsg EXCEPT ![src] = [Cmd |-> "RP_Replace"]]
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, InvMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

PI_Local_Replace ==
    /\ Proc[Home].ProcCmd = "NODE_None"
    /\ Proc[Home].CacheState = "CACHE_S"
    /\ Dir' = [Dir EXCEPT !.Local = FALSE]
    /\ Proc' = [Proc EXCEPT ![Home].CacheState = "CACHE_I", ![Home].CacheData = Undefined]
    /\ UNCHANGED <<Home, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

NI_Nak(dst) ==
    /\ UniMsg[dst].Cmd = "UNI_Nak"
    /\ UniMsg' = [UniMsg EXCEPT ![dst] = [Cmd |-> "UNI_None", Proc |-> Undefined,
                                          Data |-> Undefined]]
    /\ Proc' = [Proc EXCEPT ![dst].ProcCmd = "NODE_None", ![dst].InvMarked = FALSE]
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

NI_Nak_Clear ==
    /\ NakcMsg.Cmd = "NAKC_Nakc"
    /\ NakcMsg' = [Cmd |-> "NAKC_None"]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE]
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, RpMsg, WbMsg, ShWbMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

NI_Local_Get_Nak(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_Get"
    /\ UniMsg[src].Proc = Home
    /\ RpMsg[src].Cmd # "RP_Replace"
    /\ \/ Dir.Pending
       \/ (Dir.Dirty /\ Dir.Local /\ Proc[Home].CacheState # "CACHE_E")
       \/ (Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr = src)
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Nak", Proc |-> Home, Data |-> Undefined]]
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

NI_Local_Get_Get(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_Get"
    /\ UniMsg[src].Proc = Home
    /\ RpMsg[src].Cmd # "RP_Replace"
    /\ ~Dir.Pending /\ Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr # src
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Get", Proc |-> Dir.HeadPtr,
                                          Data |-> Undefined]]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_Get" ELSE FwdCmd
    /\ PendReqSrc' = src
    /\ PendReqCmd' = "UNI_Get"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, Proc, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, FwdSrc>>

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
                 THEN [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Put", Proc |-> Home,
                                               Data |-> Proc[Home].CacheData]]
                 ELSE [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Put", Proc |-> Home, Data |-> MemData]]
    /\ UNCHANGED <<Home, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData, PrevData,
                   pendVars, fwdVars>>

\* Remote NAK of a shared/exclusive request (merges the former
\* NI_Remote_Get_Nak / NI_Remote_GetX_Nak).
NI_Remote_Nak(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ UniMsg[src].Cmd \in {"UNI_Get", "UNI_GetX"}
    /\ UniMsg[src].Proc = dst
    /\ Proc[dst].CacheState # "CACHE_E"
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Nak", Proc |-> dst, Data |-> Undefined]]
    /\ NakcMsg' = [Cmd |-> "NAKC_Nakc"]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, CurrData,
                   PrevData, pendVars>>

NI_Remote_Get_Put(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ UniMsg[src].Cmd = "UNI_Get"
    /\ UniMsg[src].Proc = dst
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_S"]
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Put", Proc |-> dst,
                                          Data |-> Proc[dst].CacheData]]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ ShWbMsg' = IF src # Home
                  THEN [Cmd |-> "SHWB_ShWb", Proc |-> src, Data |-> Proc[dst].CacheData]
                  ELSE ShWbMsg
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars>>

NI_Local_GetX_Nak(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_GetX"
    /\ UniMsg[src].Proc = Home
    /\ \/ Dir.Pending
       \/ (Dir.Dirty /\ Dir.Local /\ Proc[Home].CacheState # "CACHE_E")
       \/ (Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr = src)
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_Nak", Proc |-> Home, Data |-> Undefined]]
    /\ UNCHANGED <<Home, Proc, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

NI_Local_GetX_GetX(src) ==
    /\ src # Home
    /\ UniMsg[src].Cmd = "UNI_GetX"
    /\ UniMsg[src].Proc = Home
    /\ ~Dir.Pending /\ Dir.Dirty /\ ~Dir.Local /\ Dir.HeadPtr # src
    /\ Dir' = [Dir EXCEPT !.Pending = TRUE]
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_GetX", Proc |-> Dir.HeadPtr,
                                          Data |-> Undefined]]
    /\ FwdCmd' = IF Dir.HeadPtr # Home THEN "UNI_GetX" ELSE FwdCmd
    /\ PendReqSrc' = src
    /\ PendReqCmd' = "UNI_GetX"
    /\ Collecting' = FALSE
    /\ UNCHANGED <<Home, Proc, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, FwdSrc>>

\* Home holds the line exclusively, so it can be handed to src directly.
NI_Local_GetX_PutX_Dirty(src) ==
    /\ Dir.Dirty
    /\ Dir' = [Dir EXCEPT !.Local = FALSE, !.Dirty = TRUE, !.HeadVld = TRUE,
                          !.HeadPtr = src, !.ShrVld = FALSE, !.ShrSet = {}, !.InvSet = {}]
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_PutX", Proc |-> Home,
                                          Data |-> Proc[Home].CacheData]]
    /\ Proc' = ProcHomeInvalid
    /\ UNCHANGED <<InvMsg, PrevData, pendVars>>

\* src is already the head and the only sharer, so nobody has to be invalidated
\* and memory's copy is handed over.
NI_Local_GetX_PutX_Grant(src) ==
    /\ ~Dir.Dirty
    /\ NoOtherSharers(src)
    /\ Dir' = [Dir EXCEPT !.Local = FALSE, !.Dirty = TRUE, !.HeadVld = TRUE,
                          !.HeadPtr = src, !.ShrVld = FALSE, !.ShrSet = {}, !.InvSet = {}]
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_PutX", Proc |-> Home, Data |-> MemData]]
    /\ Proc' = IF Dir.Local THEN ProcHomeInvalidMarked ELSE ProcHomeInvalid
    /\ UNCHANGED <<InvMsg, PrevData, pendVars>>

\* Others share the line: they are invalidated first and the request goes
\* pending until their acks come back.
NI_Local_GetX_PutX_Inv(src) ==
    /\ ~Dir.Dirty
    /\ ~NoOtherSharers(src)
    /\ Dir' = [Pending |-> TRUE, Local |-> FALSE, Dirty |-> TRUE, HeadVld |-> TRUE, HeadPtr |-> src,
               ShrVld |-> FALSE, ShrSet |-> {}, InvSet |-> InvNodes({Home, src})]
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_PutX", Proc |-> Home, Data |-> MemData]]
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
    /\ UNCHANGED <<Home, MemData, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData, fwdVars>>

NI_Remote_GetX_PutX(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ UniMsg[src].Cmd = "UNI_GetX"
    /\ UniMsg[src].Proc = dst
    /\ Proc[dst].CacheState = "CACHE_E"
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_I", ![dst].CacheData = Undefined]
    /\ UniMsg' = [UniMsg EXCEPT ![src] = [Cmd |-> "UNI_PutX", Proc |-> dst,
                                          Data |-> Proc[dst].CacheData]]
    /\ FwdCmd' = "UNI_None"
    /\ FwdSrc' = src
    /\ ShWbMsg' = IF src # Home
                  THEN [Cmd |-> "SHWB_FAck", Proc |-> src, Data |-> Undefined]
                  ELSE ShWbMsg
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars>>

NI_Local_Put ==
    /\ UniMsg[Home].Cmd = "UNI_Put"
    /\ UniMsg' = [UniMsg EXCEPT ![Home] = [Cmd |-> "UNI_None", Proc |-> Undefined,
                                           Data |-> Undefined]]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.Dirty = FALSE, !.Local = TRUE]
    /\ MemData' = UniMsg[Home].Data
    /\ Proc' = [Proc EXCEPT ![Home] = [ProcCmd |-> "NODE_None", InvMarked |-> FALSE,
                                       CacheState |-> IF Proc[Home].InvMarked THEN "CACHE_I" ELSE "CACHE_S",
                                       CacheData |-> IF Proc[Home].InvMarked THEN Undefined ELSE UniMsg[Home].Data]]
    /\ UNCHANGED <<Home, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData, PrevData,
                   pendVars, fwdVars>>

NI_Remote_Put(dst) ==
    /\ dst # Home
    /\ UniMsg[dst].Cmd = "UNI_Put"
    /\ UniMsg' = [UniMsg EXCEPT ![dst] = [Cmd |-> "UNI_None", Proc |-> Undefined,
                                          Data |-> Undefined]]
    /\ Proc' = [Proc EXCEPT ![dst] = [ProcCmd |-> "NODE_None", InvMarked |-> FALSE,
                                      CacheState |-> IF Proc[dst].InvMarked THEN "CACHE_I" ELSE "CACHE_S",
                                      CacheData |-> IF Proc[dst].InvMarked THEN Undefined ELSE UniMsg[dst].Data]]
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

NI_Local_PutXAcksDone ==
    /\ UniMsg[Home].Cmd = "UNI_PutX"
    /\ UniMsg' = [UniMsg EXCEPT ![Home] = [Cmd |-> "UNI_None", Proc |-> Undefined,
                                           Data |-> Undefined]]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.Local = TRUE, !.HeadVld = FALSE, !.HeadPtr = Undefined]
    /\ Proc' = [Proc EXCEPT ![Home] = [ProcCmd |-> "NODE_None", InvMarked |-> FALSE,
                                       CacheState |-> "CACHE_E", CacheData |-> UniMsg[Home].Data]]
    /\ UNCHANGED <<Home, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars>>

NI_Remote_PutX(dst) ==
    /\ dst # Home
    /\ UniMsg[dst].Cmd = "UNI_PutX"
    /\ Proc[dst].ProcCmd = "NODE_GetX"
    /\ UniMsg' = [UniMsg EXCEPT ![dst] = [Cmd |-> "UNI_None", Proc |-> Undefined,
                                          Data |-> Undefined]]
    /\ Proc' = [Proc EXCEPT ![dst] = [ProcCmd |-> "NODE_None", InvMarked |-> FALSE,
                                      CacheState |-> "CACHE_E", CacheData |-> UniMsg[dst].Data]]
    /\ UNCHANGED <<Home, Dir, MemData, InvMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

NI_Inv(dst) ==
    /\ dst # Home
    /\ InvMsg[dst].Cmd = "INV_Inv"
    /\ InvMsg' = [InvMsg EXCEPT ![dst] = [Cmd |-> "INV_InvAck"]]
    /\ Proc' = [Proc EXCEPT ![dst].CacheState = "CACHE_I",
                            ![dst].CacheData = Undefined,
                            ![dst].InvMarked = IF Proc[dst].ProcCmd = "NODE_Get" THEN TRUE
                                               ELSE Proc[dst].InvMarked]
    /\ UNCHANGED <<Home, Dir, MemData, UniMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

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
    /\ InvMsg' = [InvMsg EXCEPT ![src] = [Cmd |-> "INV_None"]]
    /\ \/ NI_InvAck_More(src)
       \/ NI_InvAck_Last(src)
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, RpMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, PendReqSrc, PendReqCmd, fwdVars>>

NI_Wb ==
    /\ WbMsg.Cmd = "WB_Wb"
    /\ WbMsg' = [Cmd |-> "WB_None", Proc |-> Undefined, Data |-> Undefined]
    /\ Dir' = [Dir EXCEPT !.Dirty = FALSE, !.HeadVld = FALSE, !.HeadPtr = Undefined]
    /\ MemData' = WbMsg.Data
    /\ UNCHANGED <<Home, Proc, UniMsg, InvMsg, RpMsg, ShWbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars>>

NI_FAck ==
    /\ ShWbMsg.Cmd = "SHWB_FAck"
    /\ ShWbMsg' = [Cmd |-> "SHWB_None", Proc |-> Undefined, Data |-> Undefined]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.HeadPtr = IF Dir.Dirty THEN ShWbMsg.Proc ELSE Dir.HeadPtr]
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

NI_ShWb ==
    /\ ShWbMsg.Cmd = "SHWB_ShWb"
    /\ ShWbMsg' = [Cmd |-> "SHWB_None", Proc |-> Undefined, Data |-> Undefined]
    /\ Dir' = [Dir EXCEPT !.Pending = FALSE, !.Dirty = FALSE, !.ShrVld = TRUE,
                          !.ShrSet = Dir.ShrSet \cup {ShWbMsg.Proc},
                          !.InvSet = Dir.ShrSet \cup {ShWbMsg.Proc}]
    /\ MemData' = ShWbMsg.Data
    /\ UNCHANGED <<Home, Proc, UniMsg, InvMsg, RpMsg, WbMsg, NakcMsg, CurrData,
                   PrevData, pendVars, fwdVars>>

NI_Replace(src) ==
    /\ RpMsg[src].Cmd = "RP_Replace"
    /\ RpMsg' = [RpMsg EXCEPT ![src] = [Cmd |-> "RP_None"]]
    /\ Dir' = [Dir EXCEPT !.ShrSet = IF Dir.ShrVld THEN Dir.ShrSet \ {src} ELSE Dir.ShrSet,
                          !.InvSet = IF Dir.ShrVld THEN Dir.InvSet \ {src} ELSE Dir.InvSet]
    /\ UNCHANGED <<Home, Proc, MemData, UniMsg, InvMsg, WbMsg, ShWbMsg, NakcMsg,
                   CurrData, PrevData, pendVars, fwdVars>>

-------------------------------------------------------------------------------

Next ==
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

Spec == Init /\ [][Next]_vars

\* TypeOK is defined up with the variables; its theorem has to wait for Spec.
THEOREM TypeCorrect == Spec => []TypeOK

-------------------------------------------------------------------------------
(* Progress, stated as liveness.                                              *)
(*                                                                            *)
(* Fairness is asserted per *message slot* rather than per action.  Which      *)
(* handler applies to a waiting message depends on the directory state, which  *)
(* other actions change while the message waits, so no single handler need be  *)
(* continuously enabled -- but some handler of the slot's group always is, so   *)
(* weak fairness on the group suffices and strong fairness is not needed.      *)
(* Nothing below constrains the voluntary actions -- Store and the PI_*        *)
(* request and eviction rules -- so those may happen or not.                   *)

\* Everything that can consume or rewrite the unicast message in slot n.
HandleUni(n) ==
    \/ NI_Nak(n)
    \/ NI_Local_Get_Nak(n)  \/ NI_Local_Get_Get(n)   \/ NI_Local_Get_Put(n)
    \/ NI_Local_GetX_Nak(n) \/ NI_Local_GetX_GetX(n) \/ NI_Local_GetX_PutX(n)
    \/ NI_Remote_Put(n) \/ NI_Remote_PutX(n)
    \/ (n = Home /\ (NI_Local_Put \/ NI_Local_PutXAcksDone))
    \/ \E d \in NODE : \/ NI_Remote_Nak(n, d)
                       \/ NI_Remote_Get_Put(n, d)
                       \/ NI_Remote_GetX_PutX(n, d)

\* The invalidate/ack handshake on slot n.
HandleInv(n) == NI_Inv(n) \/ NI_InvAck(n)

\* The shared-writeback slot, which also carries the forward ack.
HandleShWb == NI_FAck \/ NI_ShWb

Fairness ==
    /\ \A n \in NODE : /\ WF_vars(HandleUni(n))
                       /\ WF_vars(HandleInv(n))
                       /\ WF_vars(NI_Replace(n))
    /\ WF_vars(NI_Nak_Clear)
    /\ WF_vars(NI_Wb)
    /\ WF_vars(HandleShWb)

FairSpec == Init /\ [][Next]_vars /\ Fairness

\* No request stays outstanding forever.  This is deadlock freedom, not a claim
\* that requests succeed: a request also retires by being NAKed, so a request
\* that is endlessly NAKed and reissued satisfies it.
ReqProgress ==
    \A n \in NODE : (Proc[n].ProcCmd # "NODE_None") ~> (Proc[n].ProcCmd = "NODE_None")
THEOREM ReqProgressCorrect == FairSpec => ReqProgress

\* The directory does not stay busy forever.  Of everything here this is the
\* closest counterpart to Progress1_it11.
DirProgress == Dir.Pending ~> ~Dir.Pending
THEOREM DirProgressCorrect == FairSpec => DirProgress

\* No message is stranded in the network.
UniProgress ==
    \A n \in NODE : (UniMsg[n].Cmd # "UNI_None") ~> (UniMsg[n].Cmd = "UNI_None")
THEOREM UniProgressCorrect == FairSpec => UniProgress

InvProgress ==
    \A n \in NODE : (InvMsg[n].Cmd # "INV_None") ~> (InvMsg[n].Cmd = "INV_None")
THEOREM InvProgressCorrect == FairSpec => InvProgress

RpProgress ==
    \A n \in NODE : (RpMsg[n].Cmd = "RP_Replace") ~> (RpMsg[n].Cmd = "RP_None")
THEOREM RpProgressCorrect == FairSpec => RpProgress

WbProgress   == (WbMsg.Cmd = "WB_Wb") ~> (WbMsg.Cmd = "WB_None")
THEOREM WbProgressCorrect == FairSpec => WbProgress

ShWbProgress == (ShWbMsg.Cmd # "SHWB_None") ~> (ShWbMsg.Cmd = "SHWB_None")
THEOREM ShWbProgressCorrect == FairSpec => ShWbProgress

NakcProgress == (NakcMsg.Cmd = "NAKC_Nakc") ~> (NakcMsg.Cmd = "NAKC_None")
THEOREM NakcProgressCorrect == FairSpec => NakcProgress

\* Starvation freedom, which does NOT hold and is not checked -- it is here to
\* mark the boundary of what the properties above claim.  TLC returns a lasso in
\* which one node asks for the line, another asks too and is served, the first
\* is NAKed, retries, and the cycle repeats.  Every state of that cycle has a
\* continuation rule enabled, so the Murphi progress invariants hold throughout
\* it: an enabledness invariant cannot see starvation, only a temporal property
\* can.  Ruling the cycle out needs an arbitration assumption the protocol does
\* not make.
ReqSuccess ==
    \A n \in NODE : (Proc[n].ProcCmd = "NODE_Get") ~> (Proc[n].CacheState # "CACHE_I")

-------------------------------------------------------------------------------
(* Safety properties translated from the Murphi `invariant`s (for indep.     *)
(* cross-checking; not part of the bisimulation).                            *)

CacheStateProp ==
    \A p, q \in NODE :
        p # q => ~(Proc[p].CacheState = "CACHE_E" /\ Proc[q].CacheState = "CACHE_E")
THEOREM CacheStateCorrect == Spec => []CacheStateProp

CacheDataProp ==
    \A p \in NODE :
        /\ (Proc[p].CacheState = "CACHE_E" => Proc[p].CacheData = CurrData)
        /\ (Proc[p].CacheState = "CACHE_S" =>
              /\ (Collecting => Proc[p].CacheData = PrevData)
              /\ (~Collecting => Proc[p].CacheData = CurrData))
THEOREM CacheDataCorrect == Spec => []CacheDataProp

MemDataProp ==
    ~Dir.Dirty => MemData = CurrData
THEOREM MemDataCorrect == Spec => []MemDataProp

-------------------------------------------------------------------------------
(* The Murphi `Lemma_*` invariants.  Unlike the three properties above these  *)
(* are not statements about the protocol a user cares about: the CMP          *)
(* iteration produced them as the side conditions that made the `Other`-node  *)
(* abstraction sound, and the Murphi rules cite them by name in comments on   *)
(* the guards they justify -- guards that now live in FlashWithMutexCMP.      *)
(* They are stated here because they are invariants of the protocol, not of   *)
(* the abstraction, and because they are the natural candidates for the       *)
(* strengthening that makes the safety properties above inductive, which is   *)
(* what a TLAPS proof needs and what TLC and Apalache can check directly.     *)
(*                                                                            *)
(* Each Murphi lemma opens with `forall h : NODE do h = Home -> ...`, which   *)
(* only instantiates h to the Home node; the translations below write Home    *)
(* directly.                                                                  *)

\* An exclusive copy is unique and no grant or writeback is in flight that
\* could produce a second one.
Lemma_1 ==
    \A dst \in NODE :
        Proc[dst].CacheState = "CACHE_E" =>
            /\ Dir.Dirty
            /\ WbMsg.Cmd # "WB_Wb"
            /\ ShWbMsg.Cmd # "SHWB_ShWb"
            /\ \A p \in NODE : p # dst => Proc[p].CacheState # "CACHE_E"
            /\ UniMsg[Home].Cmd # "UNI_Put"
            /\ \A q \in NODE : UniMsg[q].Cmd # "UNI_PutX"
THEOREM Lemma_1_Correct == Spec => []Lemma_1

\* A Get that Home forwarded to a third node is the request Home is working on,
\* so the message and Home's PendReqSrc/FwdCmd agree and a rule that has one of
\* them may read off the other.
Lemma_2 ==
    \A src, dst \in NODE :
        (/\ src # dst /\ dst # Home
         /\ UniMsg[src].Cmd = "UNI_Get" /\ UniMsg[src].Proc = dst)
            => /\ Dir.Pending /\ ~Dir.Local
               /\ PendReqSrc = src /\ FwdCmd = "UNI_Get"
THEOREM Lemma_2_Correct == Spec => []Lemma_2

\* Lemma_2 for the exclusive flavour.
Lemma_3 ==
    \A src, dst \in NODE :
        (/\ src # dst /\ dst # Home
         /\ UniMsg[src].Cmd = "UNI_GetX" /\ UniMsg[src].Proc = dst)
            => /\ Dir.Pending /\ ~Dir.Local
               /\ PendReqSrc = src /\ FwdCmd = "UNI_GetX"
THEOREM Lemma_3_Correct == Spec => []Lemma_3

\* An outstanding invalidation ack pins down the rest of the network: an
\* invalidation round is open, no NAK or shared writeback is in flight, and
\* every request or grant is addressed to Home.
Lemma_4 ==
    \A p \in NODE :
        (p # Home /\ InvMsg[p].Cmd = "INV_InvAck") =>
            /\ Dir.Pending /\ Collecting
            /\ NakcMsg.Cmd = "NAKC_None" /\ ShWbMsg.Cmd = "SHWB_None"
            /\ \A q \in NODE :
                 /\ (UniMsg[q].Cmd \in {"UNI_Get", "UNI_GetX"} => UniMsg[q].Proc = Home)
                 /\ (UniMsg[q].Cmd = "UNI_PutX" => (UniMsg[q].Proc = Home /\ PendReqSrc = q))
THEOREM Lemma_4_Correct == Spec => []Lemma_4

\* An exclusive copy holds the most recently written value.  This is also the
\* first conjunct of CacheDataProp; it is restated here to keep the
\* correspondence with the Murphi invariants one-to-one.
Lemma_5 ==
    \A p \in NODE : Proc[p].CacheState = "CACHE_E" => Proc[p].CacheData = CurrData
THEOREM Lemma_5_Correct == Spec => []Lemma_5
=============================================================================
