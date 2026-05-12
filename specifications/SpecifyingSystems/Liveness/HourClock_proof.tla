-------------------------- MODULE HourClock_proof --------------------------
(***************************************************************************)
(* TLAPS proof of the theorem stated in HourClock.tla.                     *)
(***************************************************************************)
EXTENDS HourClock, TLAPS

THEOREM HCini_Invariant == HC => []HCini
<1>1. HCini => HCini
  OBVIOUS
<1>2. HCini /\ [HCnxt]_hr => HCini'
  BY DEF HCini, HCnxt
<1>. QED  BY <1>1, <1>2, PTL DEF HC

============================================================================
