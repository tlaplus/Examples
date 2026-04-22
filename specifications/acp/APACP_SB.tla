------------------------------- MODULE APACP_SB -------------------------------
(* Apalache type annotations for ACP_SB.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. The seven
   uninterpreted "tag" constants (yes, no, undecided, commit, abort,
   waiting, notsent) are typed as Str, and the configuration substitutes
   them with concrete strings. The set of participant identifiers is typed
   with the uninterpreted type PARTICIPANT. *)

CONSTANTS
  \* @type: Set(PARTICIPANT);
  participants,
  \* @type: Str;
  yes,
  \* @type: Str;
  no,
  \* @type: Str;
  undecided,
  \* @type: Str;
  commit,
  \* @type: Str;
  abort,
  \* @type: Str;
  waiting,
  \* @type: Str;
  notsent

VARIABLES
  \* @type: PARTICIPANT -> { vote: Str, alive: Bool, decision: Str, faulty: Bool, voteSent: Bool };
  participant,
  \* @type: { request: PARTICIPANT -> Bool, vote: PARTICIPANT -> Str, broadcast: PARTICIPANT -> Str, decision: Str, alive: Bool, faulty: Bool };
  coordinator

INSTANCE ACP_SB

\* Concrete value for the participants constant used by APACP_SB.cfg.
participantsVal == { "p1_OF_PARTICIPANT", "p2_OF_PARTICIPANT", "p3_OF_PARTICIPANT" }

================================================================================
