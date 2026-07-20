------------------------------ MODULE FlashWithMutex ------------------------------
(***************************************************************************)
(* A faithful, one-action-per-rule (1:1) translation of                    *)
(* ProtocolDeadlockFiles/flashWithMutex.m (the FLASH directory-based cache  *)
(* coherence protocol with the CMP "Other"-node abstraction, Env_o = TRUE). *)
(*                                                                          *)
(* Structure mirrors the Murphi model exactly: a single record variable    *)
(* Sta (the Murphi `Sta : STATE`) plus the scalar Home.  Enum values use    *)
(* the identical Murphi spelling ("CACHE_I", "UNI_Get", ...) and record     *)
(* field names are identical, so the equivalence mapping is tiny.           *)
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

DataU  == DATA \cup {Undefined}
NodeU  == ABS_NODE \cup {Undefined}
UniU   == UNI_CMD \cup {Undefined}

VARIABLES
    Home,
    Sta

vars == <<Home, Sta>>

-------------------------------------------------------------------------------

TypeOK ==
    /\ Home \in NODE
    /\ Sta.Proc \in [NODE -> [ProcCmd : NODE_CMD, InvMarked : BOOLEAN,
                              CacheState : CACHE_STATE, CacheData : DataU]]
    /\ Sta.Dir \in [Pending : BOOLEAN, Local : BOOLEAN, Dirty : BOOLEAN,
                    HeadVld : BOOLEAN, HeadPtr : NodeU, ShrVld : BOOLEAN,
                    ShrSet : [NODE -> BOOLEAN], InvSet : [NODE -> BOOLEAN]]
    /\ Sta.MemData \in DATA
    /\ Sta.UniMsg \in [NODE -> [Cmd : UNI_CMD, Proc : NodeU, Data : DataU]]
    /\ Sta.InvMsg \in [NODE -> [Cmd : INV_CMD]]
    /\ Sta.RpMsg  \in [NODE -> [Cmd : RP_CMD]]
    /\ Sta.WbMsg   \in [Cmd : WB_CMD, Proc : NodeU, Data : DataU]
    /\ Sta.ShWbMsg \in [Cmd : SHWB_CMD, Proc : NodeU, Data : DataU]
    /\ Sta.NakcMsg \in [Cmd : NAKC_CMD]
    /\ Sta.CurrData \in DATA
    /\ Sta.PrevData \in DATA
    /\ Sta.LastWrVld \in BOOLEAN
    /\ Sta.LastWrPtr \in NodeU
    /\ Sta.PendReqSrc \in NodeU
    /\ Sta.PendReqCmd \in UniU
    /\ Sta.Collecting \in BOOLEAN
    /\ Sta.FwdCmd \in UNI_CMD
    /\ Sta.FwdSrc \in NodeU
    /\ Sta.LastInvAck \in NodeU
    /\ Sta.Env_o \in BOOLEAN

-------------------------------------------------------------------------------

Init ==
    \E h \in NODE, d \in DATA :
        /\ Home = h
        /\ Sta =
            [ Proc |-> [i \in NODE |-> [ProcCmd |-> "NODE_None", InvMarked |-> FALSE,
                                        CacheState |-> "CACHE_I", CacheData |-> Undefined]],
              Dir  |-> [Pending |-> FALSE, Local |-> FALSE, Dirty |-> FALSE,
                        HeadVld |-> FALSE, HeadPtr |-> Undefined, ShrVld |-> FALSE,
                        ShrSet |-> [i \in NODE |-> FALSE], InvSet |-> [i \in NODE |-> FALSE]],
              MemData |-> d,
              UniMsg  |-> [i \in NODE |-> [Cmd |-> "UNI_None", Proc |-> Undefined, Data |-> Undefined]],
              InvMsg  |-> [i \in NODE |-> [Cmd |-> "INV_None"]],
              RpMsg   |-> [i \in NODE |-> [Cmd |-> "RP_None"]],
              WbMsg   |-> [Cmd |-> "WB_None", Proc |-> Undefined, Data |-> Undefined],
              ShWbMsg |-> [Cmd |-> "SHWB_None", Proc |-> Undefined, Data |-> Undefined],
              NakcMsg |-> [Cmd |-> "NAKC_None"],
              CurrData |-> d,
              PrevData |-> d,
              LastWrVld |-> FALSE,
              LastWrPtr |-> Undefined,
              PendReqSrc |-> Undefined,
              PendReqCmd |-> Undefined,
              Collecting |-> FALSE,
              FwdCmd |-> "UNI_None",
              FwdSrc |-> Undefined,
              LastInvAck |-> Undefined,
              Env_o |-> TRUE ]

-------------------------------------------------------------------------------
(*                        Concrete (non-ABS) rules                           *)
-------------------------------------------------------------------------------

Store(src, data) ==
    /\ Sta.Proc[src].CacheState = "CACHE_E"
    /\ Sta' = [Sta EXCEPT !.Proc[src].CacheData = data,
                          !.CurrData = data,
                          !.LastWrVld = TRUE,
                          !.LastWrPtr = src]
    /\ UNCHANGED Home

PI_Remote_Get(src) ==
    /\ src # Home
    /\ Sta.Proc[src].ProcCmd = "NODE_None"
    /\ Sta.Proc[src].CacheState = "CACHE_I"
    /\ Sta' = [Sta EXCEPT !.Proc[src].ProcCmd = "NODE_Get",
                          !.UniMsg[src].Cmd = "UNI_Get",
                          !.UniMsg[src].Proc = Home,
                          !.UniMsg[src].Data = Undefined]
    /\ UNCHANGED Home

PI_Local_Get_Get ==
    /\ Sta.Proc[Home].ProcCmd = "NODE_None"
    /\ Sta.Proc[Home].CacheState = "CACHE_I"
    /\ ~Sta.Dir.Pending /\ Sta.Dir.Dirty
    /\ Sta' = [Sta EXCEPT !.Proc[Home].ProcCmd = "NODE_Get",
                          !.Dir.Pending = TRUE,
                          !.UniMsg[Home].Cmd = "UNI_Get",
                          !.UniMsg[Home].Proc = Sta.Dir.HeadPtr,
                          !.UniMsg[Home].Data = Undefined,
                          !.FwdCmd = IF Sta.Dir.HeadPtr # Home THEN "UNI_Get" ELSE Sta.FwdCmd,
                          !.PendReqSrc = Home,
                          !.PendReqCmd = "UNI_Get",
                          !.Collecting = FALSE]
    /\ UNCHANGED Home

PI_Local_Get_Put ==
    /\ Sta.Proc[Home].ProcCmd = "NODE_None"
    /\ Sta.Proc[Home].CacheState = "CACHE_I"
    /\ ~Sta.Dir.Pending /\ ~Sta.Dir.Dirty
    /\ Sta' = [Sta EXCEPT !.Dir.Local = TRUE,
                          !.Proc[Home].ProcCmd = "NODE_None",
                          !.Proc[Home].InvMarked = FALSE,
                          !.Proc[Home].CacheState =
                              IF Sta.Proc[Home].InvMarked THEN "CACHE_I" ELSE "CACHE_S",
                          !.Proc[Home].CacheData =
                              IF Sta.Proc[Home].InvMarked THEN Undefined ELSE Sta.MemData]
    /\ UNCHANGED Home

PI_Remote_GetX(src) ==
    /\ src # Home
    /\ Sta.Proc[src].ProcCmd = "NODE_None"
    /\ Sta.Proc[src].CacheState = "CACHE_I"
    /\ Sta' = [Sta EXCEPT !.Proc[src].ProcCmd = "NODE_GetX",
                          !.UniMsg[src].Cmd = "UNI_GetX",
                          !.UniMsg[src].Proc = Home,
                          !.UniMsg[src].Data = Undefined]
    /\ UNCHANGED Home

PI_Local_GetX_GetX ==
    /\ Sta.Proc[Home].ProcCmd = "NODE_None"
    /\ Sta.Proc[Home].CacheState \in {"CACHE_I", "CACHE_S"}
    /\ ~Sta.Dir.Pending /\ Sta.Dir.Dirty
    /\ Sta' = [Sta EXCEPT !.Proc[Home].ProcCmd = "NODE_GetX",
                          !.Dir.Pending = TRUE,
                          !.UniMsg[Home].Cmd = "UNI_GetX",
                          !.UniMsg[Home].Proc = Sta.Dir.HeadPtr,
                          !.UniMsg[Home].Data = Undefined,
                          !.FwdCmd = IF Sta.Dir.HeadPtr # Home THEN "UNI_GetX" ELSE Sta.FwdCmd,
                          !.PendReqSrc = Home,
                          !.PendReqCmd = "UNI_GetX",
                          !.Collecting = FALSE]
    /\ UNCHANGED Home

PI_Local_GetX_PutX ==
    /\ Sta.Proc[Home].ProcCmd = "NODE_None"
    /\ Sta.Proc[Home].CacheState \in {"CACHE_I", "CACHE_S"}
    /\ ~Sta.Dir.Pending /\ ~Sta.Dir.Dirty
    /\ LET InvP(p) == /\ p # Home
                      /\ \/ (Sta.Dir.ShrVld /\ Sta.Dir.ShrSet[p])
                         \/ (Sta.Dir.HeadVld /\ Sta.Dir.HeadPtr = p)
           base == [Sta EXCEPT !.Dir.Local = TRUE, !.Dir.Dirty = TRUE]
           withHead ==
               IF Sta.Dir.HeadVld
               THEN [base EXCEPT !.Dir.Pending = TRUE,
                                 !.PendReqSrc = Home,
                                 !.Dir.HeadVld = FALSE,
                                 !.Dir.HeadPtr = Undefined,
                                 !.Dir.ShrVld = FALSE,
                                 !.Dir.ShrSet = [p \in NODE |-> FALSE],
                                 !.Dir.InvSet = [p \in NODE |-> InvP(p)],
                                 !.InvMsg = [p \in NODE |-> [Cmd |-> IF InvP(p) THEN "INV_Inv" ELSE "INV_None"]],
                                 !.Collecting = TRUE,
                                 !.PrevData = Sta.CurrData]
               ELSE base
       IN Sta' = [withHead EXCEPT !.Proc[Home].ProcCmd = "NODE_None",
                                  !.Proc[Home].InvMarked = FALSE,
                                  !.Proc[Home].CacheState = "CACHE_E",
                                  !.Proc[Home].CacheData = Sta.MemData]
    /\ UNCHANGED Home

PI_Remote_PutX(dst) ==
    /\ dst # Home
    /\ Sta.Proc[dst].ProcCmd = "NODE_None"
    /\ Sta.Proc[dst].CacheState = "CACHE_E"
    /\ Sta' = [Sta EXCEPT !.Proc[dst].CacheState = "CACHE_I",
                          !.Proc[dst].CacheData = Undefined,
                          !.WbMsg.Cmd = "WB_Wb",
                          !.WbMsg.Proc = dst,
                          !.WbMsg.Data = Sta.Proc[dst].CacheData]
    /\ UNCHANGED Home

PI_Local_PutX ==
    /\ Sta.Proc[Home].ProcCmd = "NODE_None"
    /\ Sta.Proc[Home].CacheState = "CACHE_E"
    /\ Sta' = [Sta EXCEPT !.Proc[Home].CacheState = "CACHE_I",
                          !.Proc[Home].CacheData = Undefined,
                          !.Dir.Dirty = FALSE,
                          !.MemData = Sta.Proc[Home].CacheData,
                          !.Dir.Local = IF Sta.Dir.Pending THEN Sta.Dir.Local ELSE FALSE]
    /\ UNCHANGED Home

PI_Remote_Replace(src) ==
    /\ src # Home
    /\ Sta.Proc[src].ProcCmd = "NODE_None"
    /\ Sta.Proc[src].CacheState = "CACHE_S"
    /\ Sta' = [Sta EXCEPT !.Proc[src].CacheState = "CACHE_I",
                          !.Proc[src].CacheData = Undefined,
                          !.RpMsg[src].Cmd = "RP_Replace"]
    /\ UNCHANGED Home

PI_Local_Replace ==
    /\ Sta.Proc[Home].ProcCmd = "NODE_None"
    /\ Sta.Proc[Home].CacheState = "CACHE_S"
    /\ Sta' = [Sta EXCEPT !.Dir.Local = FALSE,
                          !.Proc[Home].CacheState = "CACHE_I",
                          !.Proc[Home].CacheData = Undefined]
    /\ UNCHANGED Home

NI_Nak(dst) ==
    /\ Sta.UniMsg[dst].Cmd = "UNI_Nak"
    /\ Sta' = [Sta EXCEPT !.UniMsg[dst].Cmd = "UNI_None",
                          !.UniMsg[dst].Proc = Undefined,
                          !.UniMsg[dst].Data = Undefined,
                          !.Proc[dst].ProcCmd = "NODE_None",
                          !.Proc[dst].InvMarked = FALSE]
    /\ UNCHANGED Home

NI_Nak_Clear ==
    /\ Sta.NakcMsg.Cmd = "NAKC_Nakc"
    /\ Sta' = [Sta EXCEPT !.NakcMsg.Cmd = "NAKC_None", !.Dir.Pending = FALSE]
    /\ UNCHANGED Home

NI_Local_Get_Nak(src) ==
    /\ src # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_Get"
    /\ Sta.UniMsg[src].Proc = Home
    /\ Sta.RpMsg[src].Cmd # "RP_Replace"
    /\ \/ Sta.Dir.Pending
       \/ (Sta.Dir.Dirty /\ Sta.Dir.Local /\ Sta.Proc[Home].CacheState # "CACHE_E")
       \/ (Sta.Dir.Dirty /\ ~Sta.Dir.Local /\ Sta.Dir.HeadPtr = src)
    /\ Sta' = [Sta EXCEPT !.UniMsg[src].Cmd = "UNI_Nak",
                          !.UniMsg[src].Proc = Home,
                          !.UniMsg[src].Data = Undefined]
    /\ UNCHANGED Home

NI_Local_Get_Get(src) ==
    /\ src # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_Get"
    /\ Sta.UniMsg[src].Proc = Home
    /\ Sta.RpMsg[src].Cmd # "RP_Replace"
    /\ ~Sta.Dir.Pending /\ Sta.Dir.Dirty /\ ~Sta.Dir.Local /\ Sta.Dir.HeadPtr # src
    /\ Sta' = [Sta EXCEPT !.Dir.Pending = TRUE,
                          !.UniMsg[src].Cmd = "UNI_Get",
                          !.UniMsg[src].Proc = Sta.Dir.HeadPtr,
                          !.UniMsg[src].Data = Undefined,
                          !.FwdCmd = IF Sta.Dir.HeadPtr # Home THEN "UNI_Get" ELSE Sta.FwdCmd,
                          !.PendReqSrc = src,
                          !.PendReqCmd = "UNI_Get",
                          !.Collecting = FALSE]
    /\ UNCHANGED Home

NI_Local_Get_Put(src) ==
    /\ src # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_Get"
    /\ Sta.UniMsg[src].Proc = Home
    /\ Sta.RpMsg[src].Cmd # "RP_Replace"
    /\ ~Sta.Dir.Pending
    /\ (Sta.Dir.Dirty => (Sta.Dir.Local /\ Sta.Proc[Home].CacheState = "CACHE_E"))
    /\ Sta' =
         IF Sta.Dir.Dirty
         THEN [Sta EXCEPT !.Dir.Dirty = FALSE, !.Dir.HeadVld = TRUE, !.Dir.HeadPtr = src,
                          !.MemData = Sta.Proc[Home].CacheData, !.Proc[Home].CacheState = "CACHE_S",
                          !.UniMsg[src].Cmd = "UNI_Put", !.UniMsg[src].Proc = Home,
                          !.UniMsg[src].Data = Sta.Proc[Home].CacheData]
         ELSE LET s1 == IF Sta.Dir.HeadVld
                        THEN [Sta EXCEPT !.Dir.ShrVld = TRUE, !.Dir.ShrSet[src] = TRUE,
                                         !.Dir.InvSet = [p \in NODE |-> (p = src) \/ Sta.Dir.ShrSet[p]]]
                        ELSE [Sta EXCEPT !.Dir.HeadVld = TRUE, !.Dir.HeadPtr = src]
              IN [s1 EXCEPT !.UniMsg[src].Cmd = "UNI_Put", !.UniMsg[src].Proc = Home,
                            !.UniMsg[src].Data = Sta.MemData]
    /\ UNCHANGED Home

NI_Remote_Get_Nak(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_Get"
    /\ Sta.UniMsg[src].Proc = dst
    /\ Sta.Proc[dst].CacheState # "CACHE_E"
    /\ Sta' = [Sta EXCEPT !.UniMsg[src].Cmd = "UNI_Nak",
                          !.UniMsg[src].Proc = dst,
                          !.UniMsg[src].Data = Undefined,
                          !.NakcMsg.Cmd = "NAKC_Nakc",
                          !.FwdCmd = "UNI_None",
                          !.FwdSrc = src]
    /\ UNCHANGED Home

NI_Remote_Get_Put(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_Get"
    /\ Sta.UniMsg[src].Proc = dst
    /\ Sta.Proc[dst].CacheState = "CACHE_E"
    /\ LET s1 == [Sta EXCEPT !.Proc[dst].CacheState = "CACHE_S",
                             !.UniMsg[src].Cmd = "UNI_Put",
                             !.UniMsg[src].Proc = dst,
                             !.UniMsg[src].Data = Sta.Proc[dst].CacheData,
                             !.FwdCmd = "UNI_None",
                             !.FwdSrc = src]
       IN Sta' = IF src # Home
                 THEN [s1 EXCEPT !.ShWbMsg.Cmd = "SHWB_ShWb",
                                 !.ShWbMsg.Proc = src,
                                 !.ShWbMsg.Data = Sta.Proc[dst].CacheData]
                 ELSE s1
    /\ UNCHANGED Home

NI_Local_GetX_Nak(src) ==
    /\ src # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_GetX"
    /\ Sta.UniMsg[src].Proc = Home
    /\ \/ Sta.Dir.Pending
       \/ (Sta.Dir.Dirty /\ Sta.Dir.Local /\ Sta.Proc[Home].CacheState # "CACHE_E")
       \/ (Sta.Dir.Dirty /\ ~Sta.Dir.Local /\ Sta.Dir.HeadPtr = src)
    /\ Sta' = [Sta EXCEPT !.UniMsg[src].Cmd = "UNI_Nak",
                          !.UniMsg[src].Proc = Home,
                          !.UniMsg[src].Data = Undefined]
    /\ UNCHANGED Home

NI_Local_GetX_GetX(src) ==
    /\ src # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_GetX"
    /\ Sta.UniMsg[src].Proc = Home
    /\ ~Sta.Dir.Pending /\ Sta.Dir.Dirty /\ ~Sta.Dir.Local /\ Sta.Dir.HeadPtr # src
    /\ Sta' = [Sta EXCEPT !.Dir.Pending = TRUE,
                          !.UniMsg[src].Cmd = "UNI_GetX",
                          !.UniMsg[src].Proc = Sta.Dir.HeadPtr,
                          !.UniMsg[src].Data = Undefined,
                          !.FwdCmd = IF Sta.Dir.HeadPtr # Home THEN "UNI_GetX" ELSE Sta.FwdCmd,
                          !.PendReqSrc = src,
                          !.PendReqCmd = "UNI_GetX",
                          !.Collecting = FALSE]
    /\ UNCHANGED Home

NI_Local_GetX_PutX(src) ==
    /\ src # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_GetX"
    /\ Sta.UniMsg[src].Proc = Home
    /\ ~Sta.Dir.Pending
    /\ (Sta.Dir.Dirty => (Sta.Dir.Local /\ Sta.Proc[Home].CacheState = "CACHE_E"))
    /\ LET Cond3(p) == /\ p # Home /\ p # src
                       /\ \/ (Sta.Dir.ShrVld /\ Sta.Dir.ShrSet[p])
                          \/ (Sta.Dir.HeadVld /\ Sta.Dir.HeadPtr = p)
           localI(st) ==
               IF Sta.Dir.Local
               THEN [st EXCEPT !.Proc[Home].CacheState = "CACHE_I",
                               !.Proc[Home].CacheData = Undefined,
                               !.Proc[Home].InvMarked =
                                   IF Sta.Proc[Home].ProcCmd = "NODE_Get"
                                   THEN TRUE ELSE Sta.Proc[Home].InvMarked]
               ELSE st
           branch1 ==
               [Sta EXCEPT !.Dir.Local = FALSE, !.Dir.Dirty = TRUE, !.Dir.HeadVld = TRUE,
                           !.Dir.HeadPtr = src, !.Dir.ShrVld = FALSE,
                           !.Dir.ShrSet = [p \in NODE |-> FALSE],
                           !.Dir.InvSet = [p \in NODE |-> FALSE],
                           !.UniMsg[src].Cmd = "UNI_PutX", !.UniMsg[src].Proc = Home,
                           !.UniMsg[src].Data = Sta.Proc[Home].CacheData,
                           !.Proc[Home].CacheState = "CACHE_I",
                           !.Proc[Home].CacheData = Undefined]
           branch2base ==
               [Sta EXCEPT !.Dir.Local = FALSE, !.Dir.Dirty = TRUE, !.Dir.HeadVld = TRUE,
                           !.Dir.HeadPtr = src, !.Dir.ShrVld = FALSE,
                           !.Dir.ShrSet = [p \in NODE |-> FALSE],
                           !.Dir.InvSet = [p \in NODE |-> FALSE],
                           !.UniMsg[src].Cmd = "UNI_PutX", !.UniMsg[src].Proc = Home,
                           !.UniMsg[src].Data = Sta.MemData,
                           !.Proc[Home].CacheState = "CACHE_I",
                           !.Proc[Home].CacheData = Undefined]
           branch3base ==
               [Sta EXCEPT !.Dir.Pending = TRUE, !.Dir.Local = FALSE, !.Dir.Dirty = TRUE,
                           !.Dir.HeadVld = TRUE, !.Dir.HeadPtr = src, !.Dir.ShrVld = FALSE,
                           !.Dir.ShrSet = [p \in NODE |-> FALSE],
                           !.Dir.InvSet = [p \in NODE |-> Cond3(p)],
                           !.InvMsg = [p \in NODE |-> [Cmd |-> IF Cond3(p) THEN "INV_Inv" ELSE "INV_None"]],
                           !.UniMsg[src].Cmd = "UNI_PutX", !.UniMsg[src].Proc = Home,
                           !.UniMsg[src].Data = Sta.MemData,
                           !.PendReqSrc = src, !.PendReqCmd = "UNI_GetX",
                           !.Collecting = TRUE, !.PrevData = Sta.CurrData]
           elsifCond ==
               Sta.Dir.HeadVld => (Sta.Dir.HeadPtr = src
                                   /\ \A p \in NODE : p # src => ~Sta.Dir.ShrSet[p])
       IN Sta' = IF Sta.Dir.Dirty THEN branch1
                 ELSE IF elsifCond THEN localI(branch2base)
                 ELSE localI(branch3base)
    /\ UNCHANGED Home

NI_Remote_GetX_Nak(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_GetX"
    /\ Sta.UniMsg[src].Proc = dst
    /\ Sta.Proc[dst].CacheState # "CACHE_E"
    /\ Sta' = [Sta EXCEPT !.UniMsg[src].Cmd = "UNI_Nak",
                          !.UniMsg[src].Proc = dst,
                          !.UniMsg[src].Data = Undefined,
                          !.NakcMsg.Cmd = "NAKC_Nakc",
                          !.FwdCmd = "UNI_None",
                          !.FwdSrc = src]
    /\ UNCHANGED Home

NI_Remote_GetX_PutX(src, dst) ==
    /\ src # dst /\ dst # Home
    /\ Sta.UniMsg[src].Cmd = "UNI_GetX"
    /\ Sta.UniMsg[src].Proc = dst
    /\ Sta.Proc[dst].CacheState = "CACHE_E"
    /\ LET s1 == [Sta EXCEPT !.Proc[dst].CacheState = "CACHE_I",
                             !.Proc[dst].CacheData = Undefined,
                             !.UniMsg[src].Cmd = "UNI_PutX",
                             !.UniMsg[src].Proc = dst,
                             !.UniMsg[src].Data = Sta.Proc[dst].CacheData,
                             !.FwdCmd = "UNI_None",
                             !.FwdSrc = src]
       IN Sta' = IF src # Home
                 THEN [s1 EXCEPT !.ShWbMsg.Cmd = "SHWB_FAck",
                                 !.ShWbMsg.Proc = src,
                                 !.ShWbMsg.Data = Undefined]
                 ELSE s1
    /\ UNCHANGED Home

NI_Local_Put ==
    /\ Sta.UniMsg[Home].Cmd = "UNI_Put"
    /\ Sta' = [Sta EXCEPT !.UniMsg[Home].Cmd = "UNI_None",
                          !.UniMsg[Home].Proc = Undefined,
                          !.UniMsg[Home].Data = Undefined,
                          !.Dir.Pending = FALSE,
                          !.Dir.Dirty = FALSE,
                          !.Dir.Local = TRUE,
                          !.MemData = Sta.UniMsg[Home].Data,
                          !.Proc[Home].ProcCmd = "NODE_None",
                          !.Proc[Home].InvMarked = FALSE,
                          !.Proc[Home].CacheState =
                              IF Sta.Proc[Home].InvMarked THEN "CACHE_I" ELSE "CACHE_S",
                          !.Proc[Home].CacheData =
                              IF Sta.Proc[Home].InvMarked THEN Undefined ELSE Sta.UniMsg[Home].Data]
    /\ UNCHANGED Home

NI_Remote_Put(dst) ==
    /\ dst # Home
    /\ Sta.UniMsg[dst].Cmd = "UNI_Put"
    /\ Sta' = [Sta EXCEPT !.UniMsg[dst].Cmd = "UNI_None",
                          !.UniMsg[dst].Proc = Undefined,
                          !.UniMsg[dst].Data = Undefined,
                          !.Proc[dst].ProcCmd = "NODE_None",
                          !.Proc[dst].InvMarked = FALSE,
                          !.Proc[dst].CacheState =
                              IF Sta.Proc[dst].InvMarked THEN "CACHE_I" ELSE "CACHE_S",
                          !.Proc[dst].CacheData =
                              IF Sta.Proc[dst].InvMarked THEN Undefined ELSE Sta.UniMsg[dst].Data]
    /\ UNCHANGED Home

NI_Local_PutXAcksDone ==
    /\ Sta.UniMsg[Home].Cmd = "UNI_PutX"
    /\ Sta' = [Sta EXCEPT !.UniMsg[Home].Cmd = "UNI_None",
                          !.UniMsg[Home].Proc = Undefined,
                          !.UniMsg[Home].Data = Undefined,
                          !.Dir.Pending = FALSE,
                          !.Dir.Local = TRUE,
                          !.Dir.HeadVld = FALSE,
                          !.Dir.HeadPtr = Undefined,
                          !.Proc[Home].ProcCmd = "NODE_None",
                          !.Proc[Home].InvMarked = FALSE,
                          !.Proc[Home].CacheState = "CACHE_E",
                          !.Proc[Home].CacheData = Sta.UniMsg[Home].Data]
    /\ UNCHANGED Home

NI_Remote_PutX(dst) ==
    /\ dst # Home
    /\ Sta.UniMsg[dst].Cmd = "UNI_PutX"
    /\ Sta.Proc[dst].ProcCmd = "NODE_GetX"
    /\ Sta' = [Sta EXCEPT !.UniMsg[dst].Cmd = "UNI_None",
                          !.UniMsg[dst].Proc = Undefined,
                          !.UniMsg[dst].Data = Undefined,
                          !.Proc[dst].ProcCmd = "NODE_None",
                          !.Proc[dst].InvMarked = FALSE,
                          !.Proc[dst].CacheState = "CACHE_E",
                          !.Proc[dst].CacheData = Sta.UniMsg[dst].Data]
    /\ UNCHANGED Home

NI_Inv(dst) ==
    /\ dst # Home
    /\ Sta.InvMsg[dst].Cmd = "INV_Inv"
    /\ Sta' = [Sta EXCEPT !.InvMsg[dst].Cmd = "INV_InvAck",
                          !.Proc[dst].CacheState = "CACHE_I",
                          !.Proc[dst].CacheData = Undefined,
                          !.Proc[dst].InvMarked =
                              IF Sta.Proc[dst].ProcCmd = "NODE_Get" THEN TRUE
                              ELSE Sta.Proc[dst].InvMarked]
    /\ UNCHANGED Home

NI_InvAck(src) ==
    /\ src # Home
    /\ Sta.InvMsg[src].Cmd = "INV_InvAck"
    /\ Sta.Dir.Pending /\ Sta.Dir.InvSet[src]
    /\ LET s1 == [Sta EXCEPT !.InvMsg[src].Cmd = "INV_None", !.Dir.InvSet[src] = FALSE]
           moreAcks == \E p \in NODE : p # src /\ Sta.Dir.InvSet[p]
       IN Sta' = IF moreAcks
                 THEN [s1 EXCEPT !.LastInvAck = src]
                 ELSE [s1 EXCEPT !.Dir.Pending = FALSE,
                                 !.Dir.Local = IF Sta.Dir.Local /\ ~Sta.Dir.Dirty
                                               THEN FALSE ELSE Sta.Dir.Local,
                                 !.Collecting = FALSE,
                                 !.LastInvAck = src]
    /\ UNCHANGED Home

NI_Wb ==
    /\ Sta.WbMsg.Cmd = "WB_Wb"
    /\ Sta' = [Sta EXCEPT !.WbMsg.Cmd = "WB_None",
                          !.WbMsg.Proc = Undefined,
                          !.WbMsg.Data = Undefined,
                          !.Dir.Dirty = FALSE,
                          !.Dir.HeadVld = FALSE,
                          !.Dir.HeadPtr = Undefined,
                          !.MemData = Sta.WbMsg.Data]
    /\ UNCHANGED Home

NI_FAck ==
    /\ Sta.ShWbMsg.Cmd = "SHWB_FAck"
    /\ Sta' = [Sta EXCEPT !.ShWbMsg.Cmd = "SHWB_None",
                          !.ShWbMsg.Proc = Undefined,
                          !.ShWbMsg.Data = Undefined,
                          !.Dir.Pending = FALSE,
                          !.Dir.HeadPtr = IF Sta.Dir.Dirty THEN Sta.ShWbMsg.Proc ELSE Sta.Dir.HeadPtr]
    /\ UNCHANGED Home

NI_ShWb ==
    /\ Sta.ShWbMsg.Cmd = "SHWB_ShWb"
    /\ Sta' = [Sta EXCEPT !.ShWbMsg.Cmd = "SHWB_None",
                          !.ShWbMsg.Proc = Undefined,
                          !.ShWbMsg.Data = Undefined,
                          !.Dir.Pending = FALSE,
                          !.Dir.Dirty = FALSE,
                          !.Dir.ShrVld = TRUE,
                          !.Dir.ShrSet = [p \in NODE |-> (p = Sta.ShWbMsg.Proc) \/ Sta.Dir.ShrSet[p]],
                          !.Dir.InvSet = [p \in NODE |-> (p = Sta.ShWbMsg.Proc) \/ Sta.Dir.ShrSet[p]],
                          !.MemData = Sta.ShWbMsg.Data]
    /\ UNCHANGED Home

NI_Replace(src) ==
    /\ Sta.RpMsg[src].Cmd = "RP_Replace"
    /\ Sta' = [Sta EXCEPT !.RpMsg[src].Cmd = "RP_None",
                          !.Dir.ShrSet[src] = IF Sta.Dir.ShrVld THEN FALSE ELSE Sta.Dir.ShrSet[src],
                          !.Dir.InvSet[src] = IF Sta.Dir.ShrVld THEN FALSE ELSE Sta.Dir.InvSet[src]]
    /\ UNCHANGED Home

-------------------------------------------------------------------------------
(*                    ABS_* abstract-environment rules                       *)
-------------------------------------------------------------------------------
(* Shared guard fragment used by the ABS_* environment rules that summarize  *)
(* a writeback from the abstract node (Lemma_1 side condition).              *)

AbsDirtyClean ==
    /\ Sta.Dir.Dirty
    /\ Sta.WbMsg.Cmd # "WB_Wb"
    /\ Sta.ShWbMsg.Cmd # "SHWB_ShWb"
    /\ \A p \in NODE : Sta.Proc[p].CacheState # "CACHE_E"
    /\ Sta.UniMsg[Home].Cmd # "UNI_Put"
    /\ \A q \in NODE : Sta.UniMsg[q].Cmd # "UNI_PutX"

ABS_Store(data) ==
    /\ Sta.Env_o
    /\ AbsDirtyClean
    /\ Sta' = [Sta EXCEPT !.CurrData = data, !.LastWrVld = TRUE, !.LastWrPtr = Other]
    /\ UNCHANGED Home

ABS_PI_Remote_PutX ==
    /\ Sta.Env_o
    /\ AbsDirtyClean
    /\ Sta' = [Sta EXCEPT !.WbMsg.Cmd = "WB_Wb", !.WbMsg.Proc = Other, !.WbMsg.Data = Sta.CurrData]
    /\ UNCHANGED Home

ABS_NI_Local_Get_Get ==
    /\ Sta.Env_o
    /\ ~Sta.Dir.Pending /\ Sta.Dir.Dirty /\ ~Sta.Dir.Local /\ Sta.Dir.HeadPtr # Other
    /\ Sta' = [Sta EXCEPT !.Dir.Pending = TRUE,
                          !.FwdCmd = IF Sta.Dir.HeadPtr # Home THEN "UNI_Get" ELSE Sta.FwdCmd,
                          !.PendReqSrc = Other,
                          !.PendReqCmd = "UNI_Get",
                          !.Collecting = FALSE]
    /\ UNCHANGED Home

ABS_NI_Local_Get_Put ==
    /\ Sta.Env_o
    /\ ~Sta.Dir.Pending
    /\ (Sta.Dir.Dirty => (Sta.Dir.Local /\ Sta.Proc[Home].CacheState = "CACHE_E"))
    /\ Sta' =
         IF Sta.Dir.Dirty
         THEN [Sta EXCEPT !.Dir.Dirty = FALSE, !.Dir.HeadVld = TRUE, !.Dir.HeadPtr = Other,
                          !.MemData = Sta.Proc[Home].CacheData, !.Proc[Home].CacheState = "CACHE_S"]
         ELSE IF Sta.Dir.HeadVld
              THEN [Sta EXCEPT !.Dir.ShrVld = TRUE,
                               !.Dir.InvSet = [p \in NODE |-> Sta.Dir.ShrSet[p]]]
              ELSE [Sta EXCEPT !.Dir.HeadVld = TRUE, !.Dir.HeadPtr = Other]
    /\ UNCHANGED Home

ABS_NI_Remote_Get_Nak_src(dst) ==
    /\ Sta.Env_o /\ dst # Home
    /\ Sta.Proc[dst].CacheState # "CACHE_E"
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = Other /\ Sta.FwdCmd = "UNI_Get"
    /\ Sta' = [Sta EXCEPT !.NakcMsg.Cmd = "NAKC_Nakc", !.FwdCmd = "UNI_None", !.FwdSrc = Other]
    /\ UNCHANGED Home

ABS_NI_Remote_Get_Nak_dst(src) ==
    /\ Sta.Env_o
    /\ Sta.UniMsg[src].Cmd = "UNI_Get" /\ Sta.UniMsg[src].Proc = Other
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = src /\ Sta.FwdCmd = "UNI_Get"
    /\ Sta' = [Sta EXCEPT !.UniMsg[src].Cmd = "UNI_Nak",
                          !.UniMsg[src].Proc = Other,
                          !.UniMsg[src].Data = Undefined,
                          !.NakcMsg.Cmd = "NAKC_Nakc",
                          !.FwdCmd = "UNI_None",
                          !.FwdSrc = src]
    /\ UNCHANGED Home

ABS_NI_Remote_Get_Nak_src_dst ==
    /\ Sta.Env_o
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = Other /\ Sta.FwdCmd = "UNI_Get"
    /\ Sta' = [Sta EXCEPT !.NakcMsg.Cmd = "NAKC_Nakc", !.FwdCmd = "UNI_None", !.FwdSrc = Other]
    /\ UNCHANGED Home

ABS_NI_Remote_Get_Put_src(dst) ==
    /\ Sta.Env_o /\ dst # Home
    /\ Sta.Proc[dst].CacheState = "CACHE_E"
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = Other /\ Sta.FwdCmd = "UNI_Get"
    /\ Sta' = [Sta EXCEPT !.Proc[dst].CacheState = "CACHE_S",
                          !.ShWbMsg.Cmd = "SHWB_ShWb",
                          !.ShWbMsg.Proc = Other,
                          !.ShWbMsg.Data = Sta.Proc[dst].CacheData,
                          !.FwdCmd = "UNI_None",
                          !.FwdSrc = Other]
    /\ UNCHANGED Home

ABS_NI_Remote_Get_Put_dst(src) ==
    /\ Sta.Env_o
    /\ Sta.UniMsg[src].Cmd = "UNI_Get" /\ Sta.UniMsg[src].Proc = Other
    /\ AbsDirtyClean
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = src /\ Sta.FwdCmd = "UNI_Get"
    /\ LET s1 == [Sta EXCEPT !.UniMsg[src].Cmd = "UNI_Put",
                             !.UniMsg[src].Proc = Other,
                             !.UniMsg[src].Data = Sta.CurrData,
                             !.FwdCmd = "UNI_None",
                             !.FwdSrc = src]
       IN Sta' = IF src # Home
                 THEN [s1 EXCEPT !.ShWbMsg.Cmd = "SHWB_ShWb",
                                 !.ShWbMsg.Proc = src,
                                 !.ShWbMsg.Data = Sta.CurrData]
                 ELSE s1
    /\ UNCHANGED Home

ABS_NI_Remote_Get_Put_src_dst ==
    /\ Sta.Env_o
    /\ AbsDirtyClean
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = Other /\ Sta.FwdCmd = "UNI_Get"
    /\ Sta' = [Sta EXCEPT !.ShWbMsg.Cmd = "SHWB_ShWb",
                          !.ShWbMsg.Proc = Other,
                          !.ShWbMsg.Data = Sta.CurrData,
                          !.FwdCmd = "UNI_None",
                          !.FwdSrc = Other]
    /\ UNCHANGED Home

ABS_NI_Local_GetX_GetX ==
    /\ Sta.Env_o
    /\ ~Sta.Dir.Pending /\ Sta.Dir.Dirty /\ ~Sta.Dir.Local /\ Sta.Dir.HeadPtr # Other
    /\ Sta' = [Sta EXCEPT !.Dir.Pending = TRUE,
                          !.FwdCmd = IF Sta.Dir.HeadPtr # Home THEN "UNI_GetX" ELSE Sta.FwdCmd,
                          !.PendReqSrc = Other,
                          !.PendReqCmd = "UNI_GetX",
                          !.Collecting = FALSE]
    /\ UNCHANGED Home

ABS_NI_Local_GetX_PutX ==
    /\ Sta.Env_o
    /\ ~Sta.Dir.Pending
    /\ (Sta.Dir.Dirty => (Sta.Dir.Local /\ Sta.Proc[Home].CacheState = "CACHE_E"))
    /\ LET Cond3(p) == /\ p # Home
                       /\ \/ (Sta.Dir.ShrVld /\ Sta.Dir.ShrSet[p])
                          \/ (Sta.Dir.HeadVld /\ Sta.Dir.HeadPtr = p)
           localI(st) ==
               IF Sta.Dir.Local
               THEN [st EXCEPT !.Proc[Home].CacheState = "CACHE_I",
                               !.Proc[Home].CacheData = Undefined,
                               !.Proc[Home].InvMarked =
                                   IF Sta.Proc[Home].ProcCmd = "NODE_Get"
                                   THEN TRUE ELSE Sta.Proc[Home].InvMarked]
               ELSE st
           branch1 ==
               [Sta EXCEPT !.Dir.Local = FALSE, !.Dir.Dirty = TRUE, !.Dir.HeadVld = TRUE,
                           !.Dir.HeadPtr = Other, !.Dir.ShrVld = FALSE,
                           !.Dir.ShrSet = [p \in NODE |-> FALSE],
                           !.Dir.InvSet = [p \in NODE |-> FALSE],
                           !.Proc[Home].CacheState = "CACHE_I",
                           !.Proc[Home].CacheData = Undefined]
           branch2base ==
               [Sta EXCEPT !.Dir.Local = FALSE, !.Dir.Dirty = TRUE, !.Dir.HeadVld = TRUE,
                           !.Dir.HeadPtr = Other, !.Dir.ShrVld = FALSE,
                           !.Dir.ShrSet = [p \in NODE |-> FALSE],
                           !.Dir.InvSet = [p \in NODE |-> FALSE],
                           !.Proc[Home].CacheState = "CACHE_I",
                           !.Proc[Home].CacheData = Undefined]
           branch3base ==
               [Sta EXCEPT !.Dir.Pending = TRUE, !.Dir.Local = FALSE, !.Dir.Dirty = TRUE,
                           !.Dir.HeadVld = TRUE, !.Dir.HeadPtr = Other, !.Dir.ShrVld = FALSE,
                           !.Dir.ShrSet = [p \in NODE |-> FALSE],
                           !.Dir.InvSet = [p \in NODE |-> Cond3(p)],
                           !.InvMsg = [p \in NODE |-> [Cmd |-> IF Cond3(p) THEN "INV_Inv" ELSE "INV_None"]],
                           !.PendReqSrc = Other, !.PendReqCmd = "UNI_GetX",
                           !.Collecting = TRUE, !.PrevData = Sta.CurrData]
           elsifCond ==
               Sta.Dir.HeadVld => (Sta.Dir.HeadPtr = Other /\ \A p \in NODE : ~Sta.Dir.ShrSet[p])
       IN Sta' = IF Sta.Dir.Dirty THEN branch1
                 ELSE IF elsifCond THEN localI(branch2base)
                 ELSE localI(branch3base)
    /\ UNCHANGED Home

ABS_NI_Remote_GetX_Nak_src(dst) ==
    /\ Sta.Env_o /\ dst # Home
    /\ Sta.Proc[dst].CacheState # "CACHE_E"
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = Other /\ Sta.FwdCmd = "UNI_GetX"
    /\ Sta' = [Sta EXCEPT !.NakcMsg.Cmd = "NAKC_Nakc", !.FwdCmd = "UNI_None", !.FwdSrc = Other]
    /\ UNCHANGED Home

ABS_NI_Remote_GetX_Nak_dst(src) ==
    /\ Sta.Env_o
    /\ Sta.UniMsg[src].Cmd = "UNI_GetX" /\ Sta.UniMsg[src].Proc = Other
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = src /\ Sta.FwdCmd = "UNI_GetX"
    /\ Sta' = [Sta EXCEPT !.UniMsg[src].Cmd = "UNI_Nak",
                          !.UniMsg[src].Proc = Other,
                          !.UniMsg[src].Data = Undefined,
                          !.NakcMsg.Cmd = "NAKC_Nakc",
                          !.FwdCmd = "UNI_None",
                          !.FwdSrc = src]
    /\ UNCHANGED Home

ABS_NI_Remote_GetX_Nak_src_dst ==
    /\ Sta.Env_o
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = Other /\ Sta.FwdCmd = "UNI_GetX"
    /\ Sta' = [Sta EXCEPT !.NakcMsg.Cmd = "NAKC_Nakc", !.FwdCmd = "UNI_None", !.FwdSrc = Other]
    /\ UNCHANGED Home

ABS_NI_Remote_GetX_PutX_src(dst) ==
    /\ Sta.Env_o /\ dst # Home
    /\ Sta.Proc[dst].CacheState = "CACHE_E"
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = Other /\ Sta.FwdCmd = "UNI_GetX"
    /\ Sta' = [Sta EXCEPT !.Proc[dst].CacheState = "CACHE_I",
                          !.Proc[dst].CacheData = Undefined,
                          !.ShWbMsg.Cmd = "SHWB_FAck",
                          !.ShWbMsg.Proc = Other,
                          !.ShWbMsg.Data = Undefined,
                          !.FwdCmd = "UNI_None",
                          !.FwdSrc = Other]
    /\ UNCHANGED Home

ABS_NI_Remote_GetX_PutX_dst(src) ==
    /\ Sta.Env_o
    /\ Sta.UniMsg[src].Cmd = "UNI_GetX" /\ Sta.UniMsg[src].Proc = Other
    /\ AbsDirtyClean
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = src /\ Sta.FwdCmd = "UNI_GetX"
    /\ LET s1 == [Sta EXCEPT !.UniMsg[src].Cmd = "UNI_PutX",
                             !.UniMsg[src].Proc = Other,
                             !.UniMsg[src].Data = Sta.CurrData,
                             !.FwdCmd = "UNI_None",
                             !.FwdSrc = src]
       IN Sta' = IF src # Home
                 THEN [s1 EXCEPT !.ShWbMsg.Cmd = "SHWB_FAck",
                                 !.ShWbMsg.Proc = src,
                                 !.ShWbMsg.Data = Undefined]
                 ELSE s1
    /\ UNCHANGED Home

ABS_NI_Remote_GetX_PutX_src_dst ==
    /\ Sta.Env_o
    /\ AbsDirtyClean
    /\ Sta.Dir.Pending /\ ~Sta.Dir.Local
    /\ Sta.PendReqSrc = Other /\ Sta.FwdCmd = "UNI_GetX"
    /\ Sta' = [Sta EXCEPT !.ShWbMsg.Cmd = "SHWB_FAck",
                          !.ShWbMsg.Proc = Other,
                          !.ShWbMsg.Data = Undefined,
                          !.FwdCmd = "UNI_None",
                          !.FwdSrc = Other]
    /\ UNCHANGED Home

ABS_NI_InvAck ==
    /\ Sta.Env_o
    /\ Sta.Dir.Pending /\ Sta.Collecting
    /\ Sta.NakcMsg.Cmd = "NAKC_None" /\ Sta.ShWbMsg.Cmd = "SHWB_None"
    /\ \A q \in NODE :
         /\ ((Sta.UniMsg[q].Cmd = "UNI_Get" \/ Sta.UniMsg[q].Cmd = "UNI_GetX")
                => Sta.UniMsg[q].Proc = Home)
         /\ (Sta.UniMsg[q].Cmd = "UNI_PutX"
                => (Sta.UniMsg[q].Proc = Home /\ Sta.PendReqSrc = q))
    /\ LET moreAcks == \E p \in NODE : Sta.Dir.InvSet[p]
       IN Sta' = IF moreAcks
                 THEN [Sta EXCEPT !.LastInvAck = Other]
                 ELSE [Sta EXCEPT !.Dir.Pending = FALSE,
                                  !.Dir.Local = IF Sta.Dir.Local /\ ~Sta.Dir.Dirty
                                                THEN FALSE ELSE Sta.Dir.Local,
                                  !.Collecting = FALSE,
                                  !.LastInvAck = Other]
    /\ UNCHANGED Home

ABS_NI_ShWb ==
    /\ Sta.Env_o
    /\ Sta.ShWbMsg.Cmd = "SHWB_ShWb" /\ Sta.ShWbMsg.Proc = Other
    /\ Sta' = [Sta EXCEPT !.ShWbMsg.Cmd = "SHWB_None",
                          !.ShWbMsg.Proc = Undefined,
                          !.ShWbMsg.Data = Undefined,
                          !.Dir.Pending = FALSE,
                          !.Dir.Dirty = FALSE,
                          !.Dir.ShrVld = TRUE,
                          !.Dir.InvSet = [p \in NODE |-> Sta.Dir.ShrSet[p]],
                          !.MemData = Sta.ShWbMsg.Data]
    /\ UNCHANGED Home

-------------------------------------------------------------------------------

Next ==
    \/ \E src \in NODE, data \in DATA : Store(src, data)
    \/ \E data \in DATA : ABS_Store(data)
    \/ \E src \in NODE :
         \/ PI_Remote_Get(src)   \/ PI_Remote_GetX(src)
         \/ PI_Remote_Replace(src)
         \/ NI_Local_Get_Nak(src) \/ NI_Local_Get_Get(src) \/ NI_Local_Get_Put(src)
         \/ NI_Local_GetX_Nak(src) \/ NI_Local_GetX_GetX(src) \/ NI_Local_GetX_PutX(src)
         \/ NI_InvAck(src) \/ NI_Replace(src)
         \/ ABS_NI_Remote_Get_Nak_src(src)  \/ ABS_NI_Remote_Get_Nak_dst(src)
         \/ ABS_NI_Remote_Get_Put_src(src)  \/ ABS_NI_Remote_Get_Put_dst(src)
         \/ ABS_NI_Remote_GetX_Nak_src(src) \/ ABS_NI_Remote_GetX_Nak_dst(src)
         \/ ABS_NI_Remote_GetX_PutX_src(src) \/ ABS_NI_Remote_GetX_PutX_dst(src)
    \/ \E dst \in NODE :
         \/ PI_Remote_PutX(dst)
         \/ NI_Nak(dst) \/ NI_Remote_Put(dst) \/ NI_Remote_PutX(dst) \/ NI_Inv(dst)
    \/ \E src \in NODE, dst \in NODE :
         \/ NI_Remote_Get_Nak(src, dst) \/ NI_Remote_Get_Put(src, dst)
         \/ NI_Remote_GetX_Nak(src, dst) \/ NI_Remote_GetX_PutX(src, dst)
    \/ PI_Local_Get_Get \/ PI_Local_Get_Put
    \/ PI_Local_GetX_GetX \/ PI_Local_GetX_PutX
    \/ PI_Local_PutX \/ PI_Local_Replace
    \/ NI_Nak_Clear \/ NI_Local_Put \/ NI_Local_PutXAcksDone
    \/ NI_Wb \/ NI_FAck \/ NI_ShWb
    \/ ABS_PI_Remote_PutX
    \/ ABS_NI_Local_Get_Get \/ ABS_NI_Local_Get_Put
    \/ ABS_NI_Remote_Get_Nak_src_dst \/ ABS_NI_Remote_Get_Put_src_dst
    \/ ABS_NI_Local_GetX_GetX \/ ABS_NI_Local_GetX_PutX
    \/ ABS_NI_Remote_GetX_Nak_src_dst \/ ABS_NI_Remote_GetX_PutX_src_dst
    \/ ABS_NI_InvAck \/ ABS_NI_ShWb

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
(* Safety properties translated from the Murphi `invariant`s (for indep.     *)
(* cross-checking; not part of the bisimulation).                            *)

CacheStateProp ==
    \A p, q \in NODE :
        p # q => ~(Sta.Proc[p].CacheState = "CACHE_E" /\ Sta.Proc[q].CacheState = "CACHE_E")

CacheDataProp ==
    \A p \in NODE :
        /\ (Sta.Proc[p].CacheState = "CACHE_E" => Sta.Proc[p].CacheData = Sta.CurrData)
        /\ (Sta.Proc[p].CacheState = "CACHE_S" =>
              /\ (Sta.Collecting => Sta.Proc[p].CacheData = Sta.PrevData)
              /\ (~Sta.Collecting => Sta.Proc[p].CacheData = Sta.CurrData))

MemDataProp ==
    ~Sta.Dir.Dirty => Sta.MemData = Sta.CurrData
=============================================================================
