---------------------- MODULE APHourClock ----------------------
(* Apalache type annotations for HourClock.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Naturals

VARIABLE
  \* @type: Int;
  hr

INSTANCE HourClock

================================================================
