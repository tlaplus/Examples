--------------------------- MODULE spanning_proof -----------------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*                                                                         *)
(*   Spec => []SntMsg                                                      *)
(*                                                                         *)
(* SntMsg ("a non-root process whose parent has not yet been set has sent  *)
(* no messages") is inductive once we add the dual:                        *)
(*                                                                         *)
(*   SentMeansCanSend ==                                                   *)
(*     \A i,j \in Proc : <<i,j>> \in msg => (i = root \/ prnt[i] # NoPrnt) *)
(*                                                                         *)
(* (Note: the spec's `TypeOK` requires <<i, prnt[i]>> \in nbrs, but        *)
(* `nbrs` is not assumed symmetric in the spec while the protocol's        *)
(* Update(i, j) action sets prnt[i] := j from a `<<j, i>> \in msg` that    *)
(* originated in `<<j, i>> \in nbrs`.  TypeOK is therefore not a true     *)
(* invariant of `Spec` in general; we leave it alone and prove SntMsg     *)
(* without it.)                                                            *)
(***************************************************************************)
EXTENDS spanning, TLAPS

SentMeansCanSend ==
  \A i, j \in Proc :
    <<i, j>> \in msg => (i = root \/ prnt[i] # NoPrnt)

PrntDomain == DOMAIN prnt = Proc

Inv == PrntDomain /\ SntMsg /\ SentMeansCanSend

LEMMA SntMsgStep == Inv /\ [Next]_vars => Inv'
  <1>. SUFFICES ASSUME Inv, [Next]_vars  PROVE Inv'
    OBVIOUS
  <1>. USE DEF Inv, SntMsg, SentMeansCanSend, PrntDomain
  <1>. SUFFICES ASSUME Next  PROVE Inv'
    <2>. CASE UNCHANGED vars
      BY DEF vars
    <2>. QED  OBVIOUS
  <1>. PICK ii \in Proc, jj \in Proc :
          IF ii # root /\ prnt[ii] = NoPrnt /\ <<jj, ii>> \in msg
            THEN Update(ii, jj)
            ELSE \/ Send(ii) \/ Parent(ii) \/ UNCHANGED <<prnt, msg, rpt>>
    BY DEF Next
  <1>1. CASE ii # root /\ prnt[ii] = NoPrnt /\ <<jj, ii>> \in msg
    <2>. USE <1>1
    <2>1. Update(ii, jj)
      OBVIOUS
    <2>2. msg' = msg
      BY <2>1 DEF Update
    <2>3. prnt' = [prnt EXCEPT ![ii] = jj]
      BY <2>1 DEF Update
    <2>3a. DOMAIN prnt = Proc
      OBVIOUS
    <2>4. \A k \in Proc : k # ii => prnt'[k] = prnt[k]
      BY <2>3, <2>3a
    <2>5. prnt'[ii] = jj /\ jj # NoPrnt
      <3>1. ii \in Proc /\ jj \in Proc
        OBVIOUS
      <3>2. jj # NoPrnt
        BY NoPrntFact
      <3>. QED  BY <2>3, <2>3a, <3>1, <3>2
    <2>6. SntMsg'
      <3>. SUFFICES ASSUME NEW i \in Proc, NEW j \in Proc,
                            i # root, prnt'[i] = NoPrnt
                    PROVE  <<i, j>> \notin msg'
        OBVIOUS
      <3>1. i # ii
        BY <2>5
      <3>2. prnt[i] = NoPrnt
        BY <2>4, <3>1
      <3>3. <<i, j>> \notin msg
        BY <3>2
      <3>. QED  BY <2>2, <3>3
    <2>7. SentMeansCanSend'
      <3>. SUFFICES ASSUME NEW i \in Proc, NEW j \in Proc,
                           <<i, j>> \in msg'
                    PROVE  i = root \/ prnt'[i] # NoPrnt
        OBVIOUS
      <3>1. <<i, j>> \in msg
        BY <2>2
      <3>2. i = root \/ prnt[i] # NoPrnt
        BY <3>1
      <3>3. CASE i = ii
        <4>. prnt'[i] = jj /\ jj # NoPrnt
          BY <2>5, <3>3
        <4>. QED  OBVIOUS
      <3>4. CASE i # ii
        <4>. prnt'[i] = prnt[i]
          BY <2>4, <3>4
        <4>. QED  BY <3>2
      <3>. QED  BY <3>3, <3>4
    <2>8. PrntDomain'
      <3>. DOMAIN prnt' = DOMAIN [prnt EXCEPT ![ii] = jj]
        BY <2>3
      <3>. QED  BY <2>3, <2>3a
    <2>. QED  BY <2>6, <2>7, <2>8
  <1>2. CASE ~(ii # root /\ prnt[ii] = NoPrnt /\ <<jj, ii>> \in msg)
    <2>. /\ \/ Send(ii) \/ Parent(ii) \/ UNCHANGED <<prnt, msg, rpt>>
      BY <1>2
    <2>1. CASE Send(ii)
      <3>. PICK k \in Proc :
              /\ CanSend(ii, k)
              /\ <<ii, k>> \notin msg
              /\ msg' = msg \cup {<<ii, k>>}
              /\ UNCHANGED <<prnt, rpt>>
        BY <2>1 DEF Send
      <3>1. ii = root \/ prnt[ii] # NoPrnt
        BY DEF CanSend
      <3>2. prnt' = prnt
        OBVIOUS
      <3>3. SntMsg'
        <4>. SUFFICES ASSUME NEW i \in Proc, NEW j \in Proc,
                              i # root, prnt'[i] = NoPrnt
                      PROVE  <<i, j>> \notin msg'
          OBVIOUS
        <4>. prnt[i] = NoPrnt /\ i # ii
          BY <3>1, <3>2
        <4>1. <<i, j>> \notin msg
          OBVIOUS
        <4>. <<i, j>> # <<ii, k>>
          OBVIOUS
        <4>. QED  BY <4>1
      <3>4. SentMeansCanSend'
        <4>. SUFFICES ASSUME NEW i \in Proc, NEW j \in Proc,
                              <<i, j>> \in msg'
                      PROVE  i = root \/ prnt'[i] # NoPrnt
          OBVIOUS
        <4>1. <<i, j>> \in msg \/ <<i, j>> = <<ii, k>>
          OBVIOUS
        <4>2. CASE <<i, j>> \in msg
          BY <4>2, <3>2
        <4>3. CASE <<i, j>> = <<ii, k>>
          <5>. i = ii
            BY <4>3
          <5>. QED  BY <3>1, <3>2
        <4>. QED  BY <4>1, <4>2, <4>3
      <3>. QED  BY <3>3, <3>4
    <2>2. CASE Parent(ii)
      <3>1. msg' = msg /\ prnt' = prnt
        BY <2>2 DEF Parent
      <3>. QED  BY <3>1
    <2>3. CASE UNCHANGED <<prnt, msg, rpt>>
      <3>1. msg' = msg /\ prnt' = prnt
        BY <2>3
      <3>. QED  BY <3>1
    <2>. QED  BY <2>1, <2>2, <2>3
  \* SentMeansCanSend' / SntMsg' for Send case use prnt' = prnt above.
  <1>. QED  BY <1>1, <1>2

THEOREM SntMsgInv == Spec => []SntMsg
<1>1. Init => Inv
  BY DEF Init, Inv, SntMsg, SentMeansCanSend, PrntDomain
<1>2. Inv /\ [Next]_vars => Inv'
  BY SntMsgStep
<1>3. Inv => SntMsg
  BY DEF Inv
<1>. QED  BY <1>1, <1>2, <1>3, PTL DEF Spec
============================================================================
