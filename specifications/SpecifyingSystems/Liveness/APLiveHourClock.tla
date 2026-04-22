--------------------------- MODULE APLiveHourClock ---------------------------
(* Apalache type annotations for LiveHourClock.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals

VARIABLE
  \* @type: Int;
  hr

INSTANCE LiveHourClock WITH hr <- hr

==============================================================================
