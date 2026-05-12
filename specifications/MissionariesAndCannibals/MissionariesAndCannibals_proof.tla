--------------------- MODULE MissionariesAndCannibals_proof ------------------
(***************************************************************************)
(* TLAPS proof of  Spec => []TypeOK.                                       *)
(* (Solution is meant to be violated to find a solution; not a real        *)
(*  safety property.)                                                       *)
(***************************************************************************)
EXTENDS MissionariesAndCannibals, TLAPS

(***************************************************************************)
(* The spec doesn't have a Spec operator -- it's only Init /\ [][Next]_... *)
(* implicitly via the .cfg.  We define it here for the proof.              *)
(***************************************************************************)
vars == <<bank_of_boat, who_is_on_bank>>
Spec == Init /\ [][Next]_vars

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>. SUFFICES ASSUME TypeOK, [Next]_vars  PROVE TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK, vars
  <2>1. CASE Next
    <3>. PICK S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)
      BY <2>1 DEF Next
    <3>. USE DEF Move
    <3>1. bank_of_boat \in {"E", "W"}
      OBVIOUS
    <3>2. who_is_on_bank[bank_of_boat] \in SUBSET (Cannibals \cup Missionaries)
      OBVIOUS
    <3>3. S \subseteq Cannibals \cup Missionaries
      BY <3>2
    <3>4. OtherBank(bank_of_boat) \in {"E", "W"}
      BY <3>1 DEF OtherBank
    <3>5. who_is_on_bank[OtherBank(bank_of_boat)]
            \in SUBSET (Cannibals \cup Missionaries)
      BY <3>4
    <3>. DEFINE newThisBank  == who_is_on_bank[bank_of_boat] \ S
                newOtherBank == who_is_on_bank[OtherBank(bank_of_boat)] \cup S
    <3>6. newThisBank \subseteq Cannibals \cup Missionaries
      BY <3>2
    <3>7. newOtherBank \subseteq Cannibals \cup Missionaries
      BY <3>3, <3>5
    <3>8. who_is_on_bank' =
            [i \in {"E", "W"} |-> IF i = bank_of_boat THEN newThisBank
                                                       ELSE newOtherBank]
      BY <3>1
    <3>9. bank_of_boat' = OtherBank(bank_of_boat)
      OBVIOUS
    <3>10. bank_of_boat' \in {"E", "W"}
      BY <3>4, <3>9
    <3>11. who_is_on_bank' \in [{"E", "W"} -> SUBSET (Cannibals \cup Missionaries)]
      BY <3>6, <3>7, <3>8
    <3>. QED  BY <3>10, <3>11
  <2>2. CASE UNCHANGED vars
    BY <2>2
  <2>. QED  BY <2>1, <2>2
<1>. QED  BY <1>1, <1>2, PTL DEF Spec
============================================================================
