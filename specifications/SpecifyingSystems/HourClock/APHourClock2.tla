---------------------- MODULE APHourClock2 ----------------------
(* Apalache type annotations for HourClock2.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. HourClock2 is
   an alternative formulation of HourClock (using `(hr % 12) + 1` instead of
   an `IF`-`THEN`-`ELSE`); the two spec formulations are claimed equivalent
   (THEOREM HC <=> HC2). *)

EXTENDS Naturals

VARIABLE
  \* @type: Int;
  hr

INSTANCE HourClock2

================================================================
