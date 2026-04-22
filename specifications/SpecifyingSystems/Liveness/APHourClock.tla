---------------------- MODULE APHourClock ----------------------
(* Apalache type annotations for Liveness/HourClock.tla, applied via
   INSTANCE so the original spec remains free of tool-specific
   idiosyncrasies. This module is an exact duplicate of
   SpecifyingSystems/HourClock/HourClock.tla, kept here so
   Specifying-Systems chapter Liveness examples can `EXTENDS HourClock` from
   a sibling module. *)

EXTENDS Naturals

VARIABLE
  \* @type: Int;
  hr

INSTANCE HourClock

================================================================
