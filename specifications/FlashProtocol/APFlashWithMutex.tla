------------------------- MODULE APFlashWithMutex -------------------------
(* Apalache type annotations for FlashWithMutex.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies.

   Undefined is the sentinel of node-, data-, and command-valued variables
   alike, so NODE, DATA, and the command enums all have to share one type.
   Str is the only candidate, which rules out modelling nodes and data as
   uninterpreted Apalache types.

   Run bounded model checking for executions of at most 5 Next steps with:
     apalache-mc check --length=5 --config=APFlashWithMutex.cfg APFlashWithMutex.tla
   Runtime depends on the hardware and on the invariant list; manifest.json
   records the current measurement.
*)

CONSTANTS
  \* @type: Set(Str);
  NODE,
  \* @type: Set(Str);
  DATA,
  \* @type: Str;
  Other,
  \* @type: Str;
  Undefined

VARIABLES
  \* @type: Str;
  Home,
  \* @type: Str -> { ProcCmd: Str, InvMarked: Bool, CacheState: Str, CacheData: Str };
  Proc,
  \* @type: { Pending: Bool, Local: Bool, Dirty: Bool, HeadVld: Bool, HeadPtr: Str, ShrVld: Bool, ShrSet: Set(Str), InvSet: Set(Str) };
  Dir,
  \* @type: Str;
  MemData,
  \* @type: Str -> { Cmd: Str, Proc: Str, Data: Str };
  UniMsg,
  \* @type: Str -> { Cmd: Str };
  InvMsg,
  \* @type: Str -> { Cmd: Str };
  RpMsg,
  \* @type: { Cmd: Str, Proc: Str, Data: Str };
  WbMsg,
  \* @type: { Cmd: Str, Proc: Str, Data: Str };
  ShWbMsg,
  \* @type: { Cmd: Str };
  NakcMsg,
  \* @type: Str;
  CurrData,
  \* @type: Str;
  PrevData,
  \* @type: Str;
  PendReqSrc,
  \* @type: Str;
  PendReqCmd,
  \* @type: Bool;
  Collecting,
  \* @type: Str;
  FwdCmd,
  \* @type: Str;
  FwdSrc,
  \* @type: Bool;
  Env_o

\* Both components of the variable group are strings, which the type checker
\* cannot tell apart from a two-element sequence.  The group is shadowed here
\* with an annotated but otherwise identical body.
\*
\* Brittle: this trick relies on SANY tolerating a duplicate definition only
\* when the body is identical to the one in `FlashWithMutex`.  Any change to
\* the body below turns the warning into a hard "Multiple declarations"
\* error.
\* @type: <<Str, Str>>;
fwdVars == <<FwdCmd, FwdSrc>>

INSTANCE FlashWithMutex

\* Concrete values for the constants used by APFlashWithMutex.cfg.
NodeVal      == { "n1", "n2" }
DataVal      == { "d1", "d2" }
OtherVal     == "Other"
UndefinedVal == "Undefined"

==============================================================================
