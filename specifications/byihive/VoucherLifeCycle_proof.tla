------------------------ MODULE VoucherLifeCycle_proof ----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*    THEOREM VSpec => [](VTypeOK /\ VConsistent)                          *)
(* stated in VoucherLifeCycle.tla.  TypeOK and VConsistent together form   *)
(* an inductive invariant.                                                 *)
(***************************************************************************)
EXTENDS VoucherLifeCycle, TLAPS

Inv == VTypeOK /\ VConsistent

THEOREM Spec_TypeOK_Consistent == VSpec => []Inv
<1>1. VInit => Inv
  BY DEF VInit, Inv, VTypeOK, VConsistent
<1>2. Inv /\ [VNext]_<<vState, vlcState>> => Inv'
  BY DEF Inv, VTypeOK, VConsistent, VNext, Issue, Transfer, Redeem, Cancel
<1>. QED  BY <1>1, <1>2, PTL DEF VSpec, Inv

============================================================================
