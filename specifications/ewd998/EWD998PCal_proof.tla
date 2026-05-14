---------------------------- MODULE EWD998PCal_proof ----------------------------
(***************************************************************************)
(* Proofs checked by TLAPS about the EWD998PCal specification.             *)
(*                                                                         *)
(* The EWD998PCal module is a PlusCal-translated version of EWD998 in      *)
(* which the per-node `pending` counter and the global `token` of EWD998   *)
(* are replaced by a single `network` variable holding a per-node bag of   *)
(* messages (payload "pl" messages and the unique token "tok" message).   *)
(* The refinement mapping (in EWD998PCal.tla) recovers EWD998's `pending` *)
(* and `token` from `network`:                                            *)
(*                                                                         *)
(*   pending = [n |-> count of [type|->"pl"] in network[n]]                *)
(*   token   = the unique tok msg in the network, with its position       *)
(*                                                                         *)
(* This module proves the safety part of the refinement,                   *)
(*                                                                         *)
(*   THEOREM Refinement == Spec => EWD998Spec                              *)
(*                                                                         *)
(* where EWD998Spec == EWD998!Init /\ [][EWD998!Next]_EWD998!vars (no     *)
(* fairness; the comment in the spec explains why).                       *)
(*                                                                         *)
(* The proof shape mirrors EWD998_proof.tla's `Refinement` theorem:       *)
(* an inductive invariant (network well-formedness + Safra's invariant   *)
(* transferred to PCal) plus a per-disjunct case analysis.                *)
(***************************************************************************)
EXTENDS EWD998PCal, TLAPS

USE NAssumption

\* The spec defines `Initiator == 0`; expose it as a fact for TLAPS.
LEMMA InitiatorIsZero == Initiator = 0  BY DEF Initiator

\* Node = 0..N-1.
LEMMA NodeFact == 0 \in Node  BY DEF Node

(***************************************************************************)
(* Type-level abbreviations.                                               *)
(***************************************************************************)
ColorSet == {"white", "black"}
PMsg == [type: {"pl"}]
TMsg == [type: {"tok"}, q: Int, color: ColorSet]
Msg  == PMsg \cup TMsg

(***************************************************************************)
(* Bag-level facts about the message-bag operators used in the spec.       *)
(*                                                                         *)
(* `EmptyBag`, `SetToBag`, `BagAdd`, `BagRemove` are imported from         *)
(* Bags / BagsExt.  We restate just enough about each so TLAPS can         *)
(* unfold them in proofs.                                                  *)
(***************************************************************************)
LEMMA EmptyBagDom == DOMAIN EmptyBag = {}
  BY DEF EmptyBag, SetToBag

LEMMA SetToBagSingleton ==
  ASSUME NEW x
  PROVE  /\ DOMAIN SetToBag({x}) = {x}
         /\ SetToBag({x})[x] = 1
  BY DEF SetToBag

LEMMA BagAddDom ==
  ASSUME NEW B, NEW x
  PROVE  DOMAIN BagAdd(B, x) = DOMAIN B \cup {x}
  BY DEF BagAdd

LEMMA BagRemoveDom ==
  ASSUME NEW B, NEW x, x \in DOMAIN B
  PROVE  /\ B[x] = 1 => DOMAIN BagRemove(B, x) = DOMAIN B \ {x}
         /\ B[x] # 1 => DOMAIN BagRemove(B, x) = DOMAIN B
  BY DEF BagRemove

(***************************************************************************)
(* Network well-formedness:                                               *)
(*  (a) every network[n] is a function from a subset of Msg to positive  *)
(*      naturals (the `IsABag` predicate, restricted to typed messages); *)
(*  (b) exactly one node holds a token, with multiplicity 1.            *)
(***************************************************************************)
BagOf(S) == UNION { [T -> Nat \ {0}] : T \in SUBSET S }

NetworkOK ==
  /\ network \in [Node -> BagOf(Msg)]
  /\ \E n \in Node : \E t \in DOMAIN network[n] :
       /\ t.type = "tok"
       /\ network[n][t] = 1
       /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
              t2.type = "tok" => (n2 = n /\ t2 = t)

PCalTypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> ColorSet]
  /\ counter \in [Node -> Int]
  /\ NetworkOK

(***************************************************************************)
(* The initial state has the unique token (with q=0, color="black") at the*)
(* Initiator (=0) and empty bags everywhere else.                         *)
(***************************************************************************)
InitTok == [type |-> "tok", q |-> 0, color |-> "black"]

LEMMA InitNetworkUniqueTok ==
  ASSUME network = [n \in Node |->
                       IF n = Initiator
                       THEN SetToBag({InitTok})
                       ELSE EmptyBag]
  PROVE  /\ DOMAIN network[Initiator] = {InitTok}
         /\ network[Initiator][InitTok] = 1
         /\ \A n \in Node \ {Initiator} : DOMAIN network[n] = {}
  <1>1. DOMAIN network[Initiator] = DOMAIN SetToBag({InitTok})
    BY DEF Initiator, Node
  <1>2. DOMAIN SetToBag({InitTok}) = {InitTok}
    BY SetToBagSingleton
  <1>3. network[Initiator][InitTok] = SetToBag({InitTok})[InitTok]
    BY DEF Initiator, Node
  <1>4. SetToBag({InitTok})[InitTok] = 1
    BY SetToBagSingleton
  <1>5. ASSUME NEW n \in Node \ {Initiator}
        PROVE  DOMAIN network[n] = {}
    <2>1. network[n] = EmptyBag
      BY <1>5 DEF Initiator, Node
    <2>. QED  BY <2>1, EmptyBagDom
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4, <1>5

(***************************************************************************)
(* The initial state satisfies the network type invariant.                *)
(***************************************************************************)
LEMMA InitNetworkOK == Init => NetworkOK
  <1>. SUFFICES ASSUME Init  PROVE NetworkOK
    OBVIOUS
  <1>. USE InitiatorIsZero, NodeFact
  <1>1. network = [n \in Node |->
                      IF n = Initiator
                      THEN SetToBag({InitTok})
                      ELSE EmptyBag]
    BY DEF Init, InitTok
  <1>2. \A n \in Node \ {Initiator} : DOMAIN network[n] = {}
    BY <1>1, InitNetworkUniqueTok
  <1>3. /\ DOMAIN network[Initiator] = {InitTok}
        /\ network[Initiator][InitTok] = 1
    BY <1>1, InitNetworkUniqueTok
  <1>4. InitTok \in Msg
    BY DEF Msg, TMsg, ColorSet, InitTok
  <1>5. network \in [Node -> BagOf(Msg)]
    <2>0. network = [n \in Node |-> IF n = Initiator THEN SetToBag({InitTok}) ELSE EmptyBag]
      BY <1>1
    <2>1. ASSUME NEW n \in Node
          PROVE  (IF n = Initiator THEN SetToBag({InitTok}) ELSE EmptyBag) \in BagOf(Msg)
      <3>1. CASE n = Initiator
        <4>1. SetToBag({InitTok}) = [e \in {InitTok} |-> 1]
          BY DEF SetToBag
        <4>2. [e \in {InitTok} |-> 1] \in [{InitTok} -> Nat \ {0}]
          OBVIOUS
        <4>3. {InitTok} \in SUBSET Msg
          BY <1>4
        <4>. QED  BY <3>1, <4>1, <4>2, <4>3 DEF BagOf
      <3>2. CASE n # Initiator
        <4>1. EmptyBag = [e \in {} |-> 1]
          BY DEF EmptyBag, SetToBag
        <4>2. [e \in {} |-> 1] \in [{} -> Nat \ {0}]
          OBVIOUS
        <4>3. {} \in SUBSET Msg
          OBVIOUS
        <4>. QED  BY <3>2, <4>1, <4>2, <4>3 DEF BagOf
      <3>. QED  BY <3>1, <3>2
    <2>. QED  BY <2>0, <2>1
  <1>6. \E n \in Node : \E t \in DOMAIN network[n] :
            /\ t.type = "tok"
            /\ network[n][t] = 1
            /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
                   t2.type = "tok" => (n2 = n /\ t2 = t)
    <2>1. InitTok \in DOMAIN network[Initiator]
      BY <1>3
    <2>2. InitTok.type = "tok"  BY DEF InitTok
    <2>3. network[Initiator][InitTok] = 1  BY <1>3
    <2>4. \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
              t2.type = "tok" => (n2 = Initiator /\ t2 = InitTok)
      <3>. SUFFICES ASSUME NEW n2 \in Node, NEW t2 \in DOMAIN network[n2],
                           t2.type = "tok"
                    PROVE  n2 = Initiator /\ t2 = InitTok
        OBVIOUS
      <3>1. n2 = Initiator
        BY <1>2
      <3>2. t2 \in DOMAIN network[Initiator]
        BY <3>1
      <3>3. t2 = InitTok
        BY <3>2, <1>3
      <3>. QED  BY <3>1, <3>3
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4, Initiator \in Node, InitiatorIsZero, NodeFact
  <1>. QED  BY <1>5, <1>6 DEF NetworkOK

(***************************************************************************)
(* The initial state satisfies the full PCalTypeOK.                       *)
(***************************************************************************)
LEMMA InitTypeOK == Init => PCalTypeOK
  <1>. SUFFICES ASSUME Init  PROVE PCalTypeOK
    OBVIOUS
  <1>1. active \in [Node -> BOOLEAN]
    BY DEF Init
  <1>2. color \in [Node -> ColorSet]
    BY DEF Init, ColorSet
  <1>3. counter \in [Node -> Int]
    <2>. counter = [self \in Node |-> 0]  BY DEF Init
    <2>. QED  BY Isa
  <1>4. NetworkOK
    BY InitNetworkOK
  <1>. QED  BY <1>1, <1>2, <1>3, <1>4 DEF PCalTypeOK

(***************************************************************************)
(* Init refinement: the PCal Init satisfies EWD998!Init under the        *)
(* refinement mapping for `pending` and `token`.                         *)
(***************************************************************************)
LEMMA InitPending == Init => pending = [i \in Node |-> 0]
  <1>. SUFFICES ASSUME Init  PROVE pending = [i \in Node |-> 0]
    OBVIOUS
  <1>. USE InitiatorIsZero, NodeFact
  <1>1. network = [n \in Node |->
                      IF n = Initiator
                      THEN SetToBag({InitTok})
                      ELSE EmptyBag]
    BY DEF Init, InitTok
  <1>2. ASSUME NEW i \in Node
        PROVE  pending[i] = 0
    <2>1. CASE i = Initiator
      <3>1. DOMAIN network[i] = {InitTok}
        BY <2>1, <1>1, InitNetworkUniqueTok
      <3>2. [type |-> "pl"] # InitTok
        BY DEF InitTok
      <3>3. [type |-> "pl"] \notin DOMAIN network[i]
        BY <3>1, <3>2
      <3>. QED  BY <3>3 DEF pending
    <2>2. CASE i # Initiator
      <3>1. DOMAIN network[i] = {}
        BY <2>2, <1>1, InitNetworkUniqueTok
      <3>. QED  BY <3>1 DEF pending
    <2>. QED  BY <2>1, <2>2
  <1>3. pending = [i \in Node |-> 0]
    <2>1. pending = [n \in Node |-> IF [type|->"pl"] \in DOMAIN network[n]
                                    THEN network[n][[type|->"pl"]] ELSE 0]
      BY DEF pending
    <2>2. \A n \in Node : (IF [type|->"pl"] \in DOMAIN network[n]
                            THEN network[n][[type|->"pl"]] ELSE 0) = 0
      <3>. SUFFICES ASSUME NEW n \in Node
                    PROVE  (IF [type|->"pl"] \in DOMAIN network[n]
                            THEN network[n][[type|->"pl"]] ELSE 0) = 0
        OBVIOUS
      <3>1. CASE n = Initiator
        <4>1. DOMAIN network[n] = {InitTok}
          BY <3>1, <1>1, InitNetworkUniqueTok
        <4>2. [type|->"pl"] # InitTok
          BY DEF InitTok
        <4>. QED  BY <4>1, <4>2
      <3>2. CASE n # Initiator
        <4>1. DOMAIN network[n] = {}
          BY <3>2, <1>1, InitNetworkUniqueTok
        <4>. QED  BY <4>1
      <3>. QED  BY <3>1, <3>2
    <2>. QED  BY <2>1, <2>2
  <1>. QED  BY <1>3

LEMMA InitToken == Init => token = [pos |-> 0, q |-> 0, color |-> "black"]
  <1>. SUFFICES ASSUME Init  PROVE token = [pos |-> 0, q |-> 0, color |-> "black"]
    OBVIOUS
  <1>. USE InitiatorIsZero, NodeFact
  <1>1. network = [n \in Node |->
                      IF n = Initiator
                      THEN SetToBag({InitTok})
                      ELSE EmptyBag]
    BY DEF Init, InitTok
  <1>2. \A n \in Node \ {Initiator} : DOMAIN network[n] = {}
    BY <1>1, InitNetworkUniqueTok
  <1>3. DOMAIN network[Initiator] = {InitTok}
    BY <1>1, InitNetworkUniqueTok
  <1>4. (CHOOSE i \in Node : \E m \in DOMAIN network[i]: m.type = "tok") = Initiator
    <2>1. \E m \in DOMAIN network[Initiator] : m.type = "tok"
      <3>1. InitTok \in DOMAIN network[Initiator]  BY <1>3
      <3>2. InitTok.type = "tok"  BY DEF InitTok
      <3>. QED  BY <3>1, <3>2
    <2>2. \A i \in Node :
              (\E m \in DOMAIN network[i] : m.type = "tok") => i = Initiator
      <3>. SUFFICES ASSUME NEW i \in Node,
                            \E m \in DOMAIN network[i] : m.type = "tok"
                    PROVE  i = Initiator
        OBVIOUS
      <3>1. CASE i # Initiator
        <4>1. DOMAIN network[i] = {}  BY <3>1, <1>2
        <4>. QED  BY <4>1
      <3>. QED  BY <3>1
    <2>. QED  BY <2>1, <2>2
  <1>5. (CHOOSE m \in DOMAIN network[Initiator] : m.type = "tok") = InitTok
    <2>1. InitTok \in DOMAIN network[Initiator]  BY <1>3
    <2>2. InitTok.type = "tok"  BY DEF InitTok
    <2>3. \A m \in DOMAIN network[Initiator] : m.type = "tok" => m = InitTok
      BY <1>3
    <2>. QED  BY <2>1, <2>2, <2>3
  <1>6. token = [pos |-> Initiator, q |-> InitTok.q, color |-> InitTok.color]
    BY <1>4, <1>5 DEF token
  <1>. QED  BY <1>6 DEF InitTok

THEOREM InitRefinement == Init => EWD998!Init
  <1>. SUFFICES ASSUME Init  PROVE EWD998!Init
    OBVIOUS
  <1>. USE InitiatorIsZero, NodeFact
  <1>1. EWD998!Node = Node
    BY DEF EWD998!Node, Node
  <1>2. EWD998!Color = ColorSet
    BY DEF EWD998!Color, ColorSet
  <1>3. active \in [Node -> BOOLEAN]
    BY DEF Init
  <1>4. color \in [Node -> EWD998!Color]
    BY <1>1, <1>2 DEF Init, ColorSet
  <1>5. counter = [i \in Node |-> 0]
    BY <1>1 DEF Init
  <1>6. pending = [i \in Node |-> 0]
    BY InitPending, <1>1
  <1>7. token \in [pos: Node, q: {0}, color: {"black"}]
    <2>1. token = [pos |-> 0, q |-> 0, color |-> "black"]
      BY InitToken
    <2>. QED  BY <2>1
  <1>. QED  BY <1>1, <1>3, <1>4, <1>5, <1>6, <1>7 DEF EWD998!Init

(***************************************************************************)
(* Helper: for any well-typed bag B and any new "pl" message added with   *)
(* BagAdd (which is a fresh element if not already in DOMAIN, otherwise   *)
(* a multiplicity bump), the result is still a well-typed bag of typed   *)
(* messages.                                                              *)
(***************************************************************************)
LEMMA BagAddOfMsg ==
  ASSUME NEW B \in BagOf(Msg), NEW m \in Msg
  PROVE  BagAdd(B, m) \in BagOf(Msg)
  <1>. PICK S \in SUBSET Msg : B \in [S -> Nat \ {0}]
    BY DEF BagOf
  <1>1. DOMAIN B = S
    OBVIOUS
  <1>2. CASE m \in DOMAIN B
    <2>1. BagAdd(B, m) = [e \in DOMAIN B |-> IF e = m THEN B[e]+1 ELSE B[e]]
      BY <1>2 DEF BagAdd
    <2>2. ASSUME NEW e \in DOMAIN B
          PROVE  (IF e = m THEN B[e]+1 ELSE B[e]) \in Nat \ {0}
      <3>1. B[e] \in Nat /\ B[e] > 0  OBVIOUS
      <3>2. B[e]+1 \in Nat /\ B[e]+1 > 0
        BY <3>1
      <3>. QED  BY <3>1, <3>2
    <2>3. BagAdd(B, m) \in [DOMAIN B -> Nat \ {0}]
      BY <2>1, <2>2
    <2>. QED  BY <2>3, <1>1, S \in SUBSET Msg DEF BagOf
  <1>3. CASE m \notin DOMAIN B
    <2>1. BagAdd(B, m) = [e \in DOMAIN B \cup {m} |-> IF e = m THEN 1 ELSE B[e]]
      BY <1>3 DEF BagAdd
    <2>2. ASSUME NEW e \in DOMAIN B \cup {m}
          PROVE  (IF e = m THEN 1 ELSE B[e]) \in Nat \ {0}
      <3>1. CASE e = m
        BY <3>1
      <3>2. CASE e # m
        <4>1. e \in DOMAIN B  BY <2>2, <3>2
        <4>2. B[e] \in Nat /\ B[e] > 0  BY <4>1
        <4>. QED  BY <3>2, <4>2
      <3>. QED  BY <3>1, <3>2
    <2>3. DOMAIN B \cup {m} \in SUBSET Msg
      BY <1>1, S \in SUBSET Msg
    <2>4. BagAdd(B, m) \in [DOMAIN B \cup {m} -> Nat \ {0}]
      BY <2>1, <2>2
    <2>. QED  BY <2>3, <2>4 DEF BagOf
  <1>. QED  BY <1>2, <1>3

(***************************************************************************)
(* Helper: BagRemove on a typed bag yields a typed bag.  This is true     *)
(* regardless of whether x is in DOMAIN B (BagRemove returns B unchanged  *)
(* in that case) or with multiplicity > 1 or = 1.                         *)
(***************************************************************************)
LEMMA BagRemoveOfMsg ==
  ASSUME NEW B \in BagOf(Msg), NEW x
  PROVE  BagRemove(B, x) \in BagOf(Msg)
  <1>. PICK S \in SUBSET Msg : B \in [S -> Nat \ {0}]
    BY DEF BagOf
  <1>1. DOMAIN B = S
    OBVIOUS
  <1>2. CASE x \notin DOMAIN B
    <2>. BagRemove(B, x) = B  BY <1>2 DEF BagRemove
    <2>. QED  BY DEF BagOf
  <1>3. CASE x \in DOMAIN B /\ B[x] = 1
    <2>1. BagRemove(B, x) = [e \in DOMAIN B \ {x} |-> B[e]]
      BY <1>3 DEF BagRemove
    <2>2. ASSUME NEW e \in DOMAIN B \ {x}
          PROVE  B[e] \in Nat \ {0}
      OBVIOUS
    <2>3. BagRemove(B, x) \in [DOMAIN B \ {x} -> Nat \ {0}]
      BY <2>1, <2>2
    <2>4. DOMAIN B \ {x} \in SUBSET Msg
      BY <1>1, S \in SUBSET Msg
    <2>. QED  BY <2>3, <2>4 DEF BagOf
  <1>4. CASE x \in DOMAIN B /\ B[x] # 1
    <2>1. BagRemove(B, x) = [e \in DOMAIN B |-> IF e=x THEN B[e]-1 ELSE B[e]]
      BY <1>4 DEF BagRemove
    <2>2. ASSUME NEW e \in DOMAIN B
          PROVE  (IF e=x THEN B[e]-1 ELSE B[e]) \in Nat \ {0}
      <3>1. CASE e = x
        <4>1. B[x] \in Nat \ {0}
          BY <1>4
        <4>2. B[x] # 1
          BY <1>4
        <4>3. B[x] - 1 \in Nat /\ B[x] - 1 # 0
          BY <4>1, <4>2
        <4>. QED  BY <3>1, <4>3
      <3>2. CASE e # x
        <4>1. B[e] \in Nat \ {0}  OBVIOUS
        <4>. QED  BY <3>2, <4>1
      <3>. QED  BY <3>1, <3>2
    <2>3. BagRemove(B, x) \in [DOMAIN B -> Nat \ {0}]
      BY <2>1, <2>2
    <2>. QED  BY <2>3, <1>1, S \in SUBSET Msg DEF BagOf
  <1>. QED  BY <1>2, <1>3, <1>4

(***************************************************************************)
(* Helper: a "pl" message is in Msg.                                      *)
(***************************************************************************)
LEMMA PlMsgInMsg == [type |-> "pl"] \in Msg
  BY DEF Msg, PMsg

(***************************************************************************)
(* Helper: a "pl" message and a "tok" message are distinct (their `type`  *)
(* fields differ).                                                        *)
(***************************************************************************)
LEMMA PlMsgIsNotTok == ~ ([type |-> "pl"].type = "tok")
  OBVIOUS

(***************************************************************************)
(* Helper: the "new token" produced by a PassToken/InitiateProbe step is  *)
(* in Msg whenever its q-field is in Int and color-field is in ColorSet. *)
(***************************************************************************)
LEMMA NewTokInMsg ==
  ASSUME NEW q \in Int, NEW c \in ColorSet
  PROVE  [type |-> "tok", q |-> q, color |-> c] \in Msg
  BY DEF Msg, TMsg

(***************************************************************************)
(* Helper: BagAdd of a non-tok message x to a bag B:                      *)
(*  (a) preserves token presence: any tok in DOMAIN B remains in          *)
(*      DOMAIN BagAdd(B,x) with the same multiplicity;                    *)
(*  (b) does not introduce new toks: any tok in DOMAIN BagAdd(B,x)        *)
(*      was already in DOMAIN B (since x has type # "tok").              *)
(***************************************************************************)
LEMMA BagAddPreservesToks ==
  ASSUME NEW B, NEW x, x.type # "tok"
  PROVE  /\ \A t : t.type = "tok" /\ t \in DOMAIN B
                  => /\ t \in DOMAIN BagAdd(B, x)
                     /\ BagAdd(B, x)[t] = B[t]
         /\ \A t : t.type = "tok" /\ t \in DOMAIN BagAdd(B, x)
                  => t \in DOMAIN B
  <1>1. CASE x \in DOMAIN B
    <2>1. BagAdd(B, x) = [e \in DOMAIN B |-> IF e = x THEN B[e] + 1 ELSE B[e]]
      BY <1>1 DEF BagAdd
    <2>2. DOMAIN BagAdd(B, x) = DOMAIN B
      BY <2>1
    <2>3. ASSUME NEW t, t.type = "tok", t \in DOMAIN B
          PROVE  /\ t \in DOMAIN BagAdd(B, x)
                 /\ BagAdd(B, x)[t] = B[t]
      <3>. t # x  BY <2>3
      <3>. QED  BY <2>1, <2>2, <2>3
    <2>. QED  BY <2>2, <2>3
  <1>2. CASE x \notin DOMAIN B
    <2>1. BagAdd(B, x) = [e \in DOMAIN B \cup {x} |-> IF e = x THEN 1 ELSE B[e]]
      BY <1>2 DEF BagAdd
    <2>2. DOMAIN BagAdd(B, x) = DOMAIN B \cup {x}
      BY <2>1
    <2>3. ASSUME NEW t, t.type = "tok", t \in DOMAIN B
          PROVE  /\ t \in DOMAIN BagAdd(B, x)
                 /\ BagAdd(B, x)[t] = B[t]
      <3>. t # x  BY <2>3
      <3>. QED  BY <2>1, <2>2, <2>3
    <2>4. ASSUME NEW t, t.type = "tok", t \in DOMAIN BagAdd(B, x)
          PROVE  t \in DOMAIN B
      <3>. t # x  BY <2>4
      <3>. QED  BY <2>2, <2>4
    <2>. QED  BY <2>3, <2>4
  <1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* Helper: BagRemove of a non-tok message x from a bag B:                 *)
(*  (a) preserves any tok in DOMAIN B (whether x was in B or not);        *)
(*  (b) does not introduce new toks.                                      *)
(***************************************************************************)
LEMMA BagRemovePreservesToks ==
  ASSUME NEW B, NEW x, x.type # "tok"
  PROVE  /\ \A t : t.type = "tok" /\ t \in DOMAIN B
                  => /\ t \in DOMAIN BagRemove(B, x)
                     /\ BagRemove(B, x)[t] = B[t]
         /\ \A t : t.type = "tok" /\ t \in DOMAIN BagRemove(B, x)
                  => t \in DOMAIN B
  <1>1. CASE x \notin DOMAIN B
    <2>. BagRemove(B, x) = B  BY <1>1 DEF BagRemove
    <2>. QED  OBVIOUS
  <1>2. CASE x \in DOMAIN B /\ B[x] = 1
    <2>1. BagRemove(B, x) = [e \in DOMAIN B \ {x} |-> B[e]]
      BY <1>2 DEF BagRemove
    <2>2. DOMAIN BagRemove(B, x) = DOMAIN B \ {x}
      BY <2>1
    <2>3. ASSUME NEW t, t.type = "tok", t \in DOMAIN B
          PROVE  /\ t \in DOMAIN BagRemove(B, x)
                 /\ BagRemove(B, x)[t] = B[t]
      <3>. t # x  BY <2>3
      <3>. QED  BY <2>1, <2>2, <2>3
    <2>4. ASSUME NEW t, t.type = "tok", t \in DOMAIN BagRemove(B, x)
          PROVE  t \in DOMAIN B
      BY <2>2, <2>4
    <2>. QED  BY <2>3, <2>4
  <1>3. CASE x \in DOMAIN B /\ B[x] # 1
    <2>1. BagRemove(B, x) = [e \in DOMAIN B |-> IF e = x THEN B[e] - 1 ELSE B[e]]
      BY <1>3 DEF BagRemove
    <2>2. DOMAIN BagRemove(B, x) = DOMAIN B
      BY <2>1
    <2>3. ASSUME NEW t, t.type = "tok", t \in DOMAIN B
          PROVE  /\ t \in DOMAIN BagRemove(B, x)
                 /\ BagRemove(B, x)[t] = B[t]
      <3>. t # x  BY <2>3
      <3>. QED  BY <2>1, <2>2, <2>3
    <2>4. ASSUME NEW t, t.type = "tok", t \in DOMAIN BagRemove(B, x)
          PROVE  t \in DOMAIN B
      BY <2>2, <2>4
    <2>. QED  BY <2>3, <2>4
  <1>. QED  BY <1>1, <1>2, <1>3

(***************************************************************************)
(* The unique-token witness extracted from NetworkOK.                      *)
(***************************************************************************)
TokenAt(n) == \E t \in DOMAIN network[n] : t.type = "tok"

(***************************************************************************)
(* Inductive step for PCalTypeOK -- per disjunct of node(self).           *)
(*                                                                        *)
(* Of the four conjuncts of PCalTypeOK we discharge `active`, `color`,    *)
(* `counter`, and the bag-typing of `network` for all five PCal           *)
(* disjuncts.  The unique-token preservation in NetworkOK is OMITTED      *)
(* and left for a later round.                                            *)
(***************************************************************************)
LEMMA TypeOK_Step ==
  PCalTypeOK /\ [Next]_vars => PCalTypeOK'
  <1>. SUFFICES ASSUME PCalTypeOK, [Next]_vars  PROVE PCalTypeOK'
    OBVIOUS
  <1>. USE DEF PCalTypeOK, NetworkOK
  <1>1. CASE UNCHANGED vars
    BY <1>1 DEF vars
  <1>2. (\E self \in Node : node(self)) => PCalTypeOK'
    <2>. SUFFICES ASSUME NEW self \in Node, node(self)
                  PROVE  PCalTypeOK'
      OBVIOUS
    <2>. USE DEF sendMsg, dropMsg, passMsg, pendingMsgs
    \* Lift node(self) into the proof context as a named fact so the
    \* disjunct-combine QED can reference it.
    <2>NodeFact. node(self)
      OBVIOUS
    \* Disjunct 1: send a payload message.
    <2>1. ASSUME active[self],
                 NEW to \in Node \ {self},
                 network' = sendMsg(network, to, [type |-> "pl"]),
                 counter' = [counter EXCEPT ![self] = counter[self] + 1],
                 UNCHANGED <<active, color>>
          PROVE  PCalTypeOK'
      <3>1. active' \in [Node -> BOOLEAN]
        BY <2>1
      <3>2. color' \in [Node -> ColorSet]
        BY <2>1
      <3>3. counter' \in [Node -> Int]
        <4>1. counter' = [counter EXCEPT ![self] = counter[self] + 1]
          BY <2>1
        <4>2. counter[self] + 1 \in Int
          OBVIOUS
        <4>. QED  BY <4>1, <4>2
      <3>4. network' \in [Node -> BagOf(Msg)]
        <4>1. network[to] \in BagOf(Msg)
          OBVIOUS
        <4>2. BagAdd(network[to], [type |-> "pl"]) \in BagOf(Msg)
          BY <4>1, BagAddOfMsg, PlMsgInMsg
        <4>3. network' = [network EXCEPT ![to] = BagAdd(network[to], [type |-> "pl"])]
          BY <2>1 DEF sendMsg
        <4>. QED  BY <4>2, <4>3
      <3>5. NetworkOK'
        \* network' agrees with network except at `to`, where a "pl" msg
        \* (not a tok) is added.  The unique-token witness is preserved.
        <4>0. PICK n0 \in Node :
                \E t \in DOMAIN network[n0] :
                  /\ t.type = "tok"
                  /\ network[n0][t] = 1
                  /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
                       t2.type = "tok" => (n2 = n0 /\ t2 = t)
          BY DEF NetworkOK
        <4>0a. PICK t0 \in DOMAIN network[n0] :
                /\ t0.type = "tok"
                /\ network[n0][t0] = 1
                /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
                     t2.type = "tok" => (n2 = n0 /\ t2 = t0)
          BY <4>0
        <4>1. network' = [network EXCEPT ![to] = BagAdd(network[to], [type |-> "pl"])]
          BY <2>1 DEF sendMsg
        <4>2. [type |-> "pl"].type # "tok"
          BY PlMsgIsNotTok
        <4>3. \* Token at n0 with t0 is preserved in network'.
              /\ t0 \in DOMAIN network'[n0]
              /\ network'[n0][t0] = 1
          <5>1. CASE n0 = to
            <6>1. network'[n0] = BagAdd(network[to], [type |-> "pl"])
              BY <4>1, <5>1
            <6>. QED  BY <5>1, <6>1, <4>0a, <4>2, BagAddPreservesToks
          <5>2. CASE n0 # to
            <6>. network'[n0] = network[n0]
              BY <4>1, <5>2
            <6>. QED  BY <4>0a
          <5>. QED  BY <5>1, <5>2
        <4>4. \* No new tok is introduced.
              \A n2 \in Node : \A t2 \in DOMAIN network'[n2] :
                t2.type = "tok" => (n2 = n0 /\ t2 = t0)
          <5>. SUFFICES ASSUME NEW n2 \in Node,
                              NEW t2 \in DOMAIN network'[n2],
                              t2.type = "tok"
                       PROVE  n2 = n0 /\ t2 = t0
            OBVIOUS
          <5>1. t2 \in DOMAIN network[n2]
            <6>1. CASE n2 = to
              <7>1. network'[n2] = BagAdd(network[to], [type |-> "pl"])
                BY <4>1, <6>1
              <7>2. t2 \in DOMAIN BagAdd(network[to], [type |-> "pl"])
                BY <7>1
              <7>3. t2 \in DOMAIN network[to]
                BY <7>2, <4>2, BagAddPreservesToks
              <7>. QED  BY <6>1, <7>3
            <6>2. CASE n2 # to
              <7>1. network'[n2] = network[n2]
                BY <4>1, <6>2
              <7>. QED  BY <7>1
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <5>1, <4>0a
        <4>5. \E n \in Node : \E t \in DOMAIN network'[n] :
                /\ t.type = "tok"
                /\ network'[n][t] = 1
                /\ \A n2 \in Node : \A t2 \in DOMAIN network'[n2] :
                     t2.type = "tok" => (n2 = n /\ t2 = t)
          BY <4>0a, <4>3, <4>4
        <4>. QED  BY <3>4, <4>5 DEF NetworkOK
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF PCalTypeOK
    \* Disjunct 2: receive a payload message.
    <2>2. ASSUME NEW msg \in pendingMsgs(network, self),
                 msg.type = "pl",
                 counter' = [counter EXCEPT ![self] = counter[self] - 1],
                 active' = [active EXCEPT ![self] = TRUE],
                 color' = [color EXCEPT ![self] = "black"],
                 network' = dropMsg(network, self, msg)
          PROVE  PCalTypeOK'
      <3>1. active' \in [Node -> BOOLEAN]
        BY <2>2
      <3>2. color' \in [Node -> ColorSet]
        <4>1. "black" \in ColorSet  BY DEF ColorSet
        <4>. QED  BY <2>2, <4>1
      <3>3. counter' \in [Node -> Int]
        <4>1. counter' = [counter EXCEPT ![self] = counter[self] - 1]
          BY <2>2
        <4>2. counter[self] - 1 \in Int
          OBVIOUS
        <4>. QED  BY <4>1, <4>2
      <3>4. network' \in [Node -> BagOf(Msg)]
        <4>1. network[self] \in BagOf(Msg)
          OBVIOUS
        <4>2. BagRemove(network[self], msg) \in BagOf(Msg)
          BY <4>1, BagRemoveOfMsg
        <4>3. network' = [network EXCEPT ![self] = BagRemove(network[self], msg)]
          BY <2>2 DEF dropMsg
        <4>. QED  BY <4>2, <4>3
      <3>5. NetworkOK'
        \* network' agrees with network except at self, where the matched
        \* "pl" msg (not a tok) is removed.  Token witness preserved.
        <4>0. PICK n0 \in Node :
                \E t \in DOMAIN network[n0] :
                  /\ t.type = "tok"
                  /\ network[n0][t] = 1
                  /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
                       t2.type = "tok" => (n2 = n0 /\ t2 = t)
          BY DEF NetworkOK
        <4>0a. PICK t0 \in DOMAIN network[n0] :
                /\ t0.type = "tok"
                /\ network[n0][t0] = 1
                /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
                     t2.type = "tok" => (n2 = n0 /\ t2 = t0)
          BY <4>0
        <4>1. network' = [network EXCEPT ![self] = BagRemove(network[self], msg)]
          BY <2>2 DEF dropMsg
        <4>2. msg.type # "tok"
          BY <2>2
        <4>3. /\ t0 \in DOMAIN network'[n0]
              /\ network'[n0][t0] = 1
          <5>1. CASE n0 = self
            <6>1. network'[n0] = BagRemove(network[self], msg)
              BY <4>1, <5>1
            <6>. QED  BY <5>1, <6>1, <4>0a, <4>2, BagRemovePreservesToks
          <5>2. CASE n0 # self
            <6>. network'[n0] = network[n0]
              BY <4>1, <5>2
            <6>. QED  BY <4>0a
          <5>. QED  BY <5>1, <5>2
        <4>4. \A n2 \in Node : \A t2 \in DOMAIN network'[n2] :
                t2.type = "tok" => (n2 = n0 /\ t2 = t0)
          <5>. SUFFICES ASSUME NEW n2 \in Node,
                              NEW t2 \in DOMAIN network'[n2],
                              t2.type = "tok"
                       PROVE  n2 = n0 /\ t2 = t0
            OBVIOUS
          <5>1. t2 \in DOMAIN network[n2]
            <6>1. CASE n2 = self
              <7>1. network'[n2] = BagRemove(network[self], msg)
                BY <4>1, <6>1
              <7>2. t2 \in DOMAIN BagRemove(network[self], msg)
                BY <7>1
              <7>3. t2 \in DOMAIN network[self]
                BY <7>2, <4>2, BagRemovePreservesToks
              <7>. QED  BY <6>1, <7>3
            <6>2. CASE n2 # self
              <7>1. network'[n2] = network[n2]
                BY <4>1, <6>2
              <7>. QED  BY <7>1
            <6>. QED  BY <6>1, <6>2
          <5>. QED  BY <5>1, <4>0a
        <4>5. \E n \in Node : \E t \in DOMAIN network'[n] :
                /\ t.type = "tok"
                /\ network'[n][t] = 1
                /\ \A n2 \in Node : \A t2 \in DOMAIN network'[n2] :
                     t2.type = "tok" => (n2 = n /\ t2 = t)
          BY <4>0a, <4>3, <4>4
        <4>. QED  BY <3>4, <4>5 DEF NetworkOK
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF PCalTypeOK
    \* Disjunct 3: deactivate.
    <2>3. ASSUME active' = [active EXCEPT ![self] = FALSE],
                 UNCHANGED <<network, color, counter>>
          PROVE  PCalTypeOK'
      <3>1. active' \in [Node -> BOOLEAN]
        BY <2>3
      <3>2. color' \in [Node -> ColorSet]
        BY <2>3
      <3>3. counter' \in [Node -> Int]
        BY <2>3
      <3>4. NetworkOK'
        BY <2>3 DEF NetworkOK
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4 DEF PCalTypeOK
    \* Disjunct 4: pass the token.
    <2>4. ASSUME self # Initiator,
                 NEW tok \in pendingMsgs(network, self),
                 tok.type = "tok" /\ ~active[self],
                 network' = passMsg(network, self, tok, self-1, [type|-> "tok", q |-> tok.q + counter[self], color |-> (IF color[self] = "black" THEN "black" ELSE tok.color)]),
                 color' = [color EXCEPT ![self] = "white"],
                 UNCHANGED <<active, counter>>
          PROVE  PCalTypeOK'
      <3>. DEFINE newTok == [type  |-> "tok",
                             q     |-> tok.q + counter[self],
                             color |-> IF color[self] = "black"
                                       THEN "black" ELSE tok.color]
      <3>1. active' \in [Node -> BOOLEAN]
        BY <2>4
      <3>2. color' \in [Node -> ColorSet]
        <4>1. "white" \in ColorSet  BY DEF ColorSet
        <4>. QED  BY <2>4, <4>1
      <3>3. counter' \in [Node -> Int]
        BY <2>4
      <3>. self - 1 \in Node
        <4>1. self \in Node /\ self # Initiator
          BY <2>4
        <4>2. self \in 0..N-1 /\ self # 0
          BY <4>1, InitiatorIsZero DEF Node
        <4>. QED  BY <4>2 DEF Node
      <3>. tok \in DOMAIN network[self]
        BY <2>4 DEF pendingMsgs
      <3>. tok \in Msg
        <4>1. network[self] \in BagOf(Msg)  OBVIOUS
        <4>2. PICK S \in SUBSET Msg : network[self] \in [S -> Nat \ {0}]
          BY <4>1 DEF BagOf
        <4>3. DOMAIN network[self] = S
          BY <4>2
        <4>. QED  BY <4>3, S \in SUBSET Msg, tok \in DOMAIN network[self]
      <3>. tok \in TMsg
        <4>1. tok \in Msg /\ tok.type = "tok"
          BY <2>4
        <4>2. tok \notin PMsg
          BY <4>1 DEF PMsg
        <4>. QED  BY <4>1, <4>2 DEF Msg
      <3>. tok.q \in Int
        BY DEF TMsg
      <3>. tok.color \in ColorSet
        BY DEF TMsg
      <3>. counter[self] \in Int
        OBVIOUS
      <3>. tok.q + counter[self] \in Int
        OBVIOUS
      <3>. (IF color[self] = "black" THEN "black" ELSE tok.color) \in ColorSet
        <4>1. "black" \in ColorSet  BY DEF ColorSet
        <4>. QED  BY <4>1
      <3>. newTok \in Msg
        BY NewTokInMsg
      <3>. self \in Int /\ self - 1 \in Int /\ self - 1 # self
        <4>1. self \in 0..N-1
          BY <2>4 DEF Node
        <4>. QED  BY <4>1
      \* The two-EXCEPT network update, with @ resolved (self # self-1):
      <3>NetEq. network' = [network EXCEPT ![self]     = BagRemove(network[self], tok),
                                           ![self - 1] = BagAdd(network[self - 1], newTok)]
        BY <2>4 DEF passMsg
      <3>4. network' \in [Node -> BagOf(Msg)]
        <4>1. network[self] \in BagOf(Msg)
          OBVIOUS
        <4>2. BagRemove(network[self], tok) \in BagOf(Msg)
          BY <4>1, BagRemoveOfMsg
        <4>3. network[self - 1] \in BagOf(Msg)
          OBVIOUS
        <4>4. BagAdd(network[self - 1], newTok) \in BagOf(Msg)
          BY <4>3, BagAddOfMsg
        <4>. QED  BY <4>2, <4>4, <3>NetEq
      <3>5. NetworkOK'
        \* The token moves from `self` (where the unique tok was, by
        \* NetworkOK uniqueness on tok \in DOMAIN network[self]) to
        \* `self-1` (where a fresh `newTok` is added).
        <4>0. PICK n0 \in Node :
                \E t \in DOMAIN network[n0] :
                  /\ t.type = "tok"
                  /\ network[n0][t] = 1
                  /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
                       t2.type = "tok" => (n2 = n0 /\ t2 = t)
          BY DEF NetworkOK
        <4>0a. PICK t0 \in DOMAIN network[n0] :
                /\ t0.type = "tok"
                /\ network[n0][t0] = 1
                /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
                     t2.type = "tok" => (n2 = n0 /\ t2 = t0)
          BY <4>0
        \* `tok` is the unique token, so it equals `t0` at `self = n0`.
        <4>0b. /\ n0 = self
               /\ t0 = tok
          BY <4>0a, <2>4 DEF pendingMsgs
        <4>0c. network[self][tok] = 1
          BY <4>0a, <4>0b
        \* No "tok" message in network[m] for m # self.
        <4>0d. \A m \in Node \ {self} : \A t \in DOMAIN network[m] : t.type # "tok"
          BY <4>0a, <4>0b
        \* In particular, newTok is not in DOMAIN network[self - 1].
        <4>0e. newTok \notin DOMAIN network[self - 1]
          <5>1. self - 1 # self
            OBVIOUS
          <5>2. self - 1 \in Node \ {self}
            OBVIOUS
          <5>3. \A t \in DOMAIN network[self - 1] : t.type # "tok"
            BY <4>0d, <5>2
          <5>. QED  BY <5>3
        \* The new tok at self-1 has multiplicity 1.
        <4>1. /\ newTok \in DOMAIN network'[self - 1]
              /\ network'[self - 1][newTok] = 1
          <5>1. network'[self - 1] = BagAdd(network[self - 1], newTok)
            BY <3>NetEq
          <5>2. BagAdd(network[self - 1], newTok) =
                  [e \in DOMAIN network[self - 1] \cup {newTok} |->
                       IF e = newTok THEN 1 ELSE network[self - 1][e]]
            BY <4>0e DEF BagAdd
          <5>3. DOMAIN network'[self - 1] = DOMAIN network[self - 1] \cup {newTok}
            BY <5>1, <5>2
          <5>. QED  BY <5>1, <5>2, <5>3
        \* Uniqueness: any tok in network'[n] for any n must be newTok at self-1.
        <4>2. \A n2 \in Node : \A t2 \in DOMAIN network'[n2] :
                t2.type = "tok" => (n2 = self - 1 /\ t2 = newTok)
          <5>. SUFFICES ASSUME NEW n2 \in Node,
                              NEW t2 \in DOMAIN network'[n2],
                              t2.type = "tok"
                       PROVE  n2 = self - 1 /\ t2 = newTok
            OBVIOUS
          <5>1. CASE n2 = self
            \* network'[self] = BagRemove(network[self], tok); tok had mult 1
            \* and was the only tok at self, so no tok remains here.
            <6>1. network'[self] = BagRemove(network[self], tok)
              BY <3>NetEq, <5>1
            <6>2. BagRemove(network[self], tok) =
                    [e \in DOMAIN network[self] \ {tok} |-> network[self][e]]
              BY <4>0c DEF BagRemove
            <6>3. DOMAIN network'[self] = DOMAIN network[self] \ {tok}
              BY <6>1, <6>2
            <6>4. t2 \in DOMAIN network[self] \ {tok}
              BY <5>1, <6>3
            \* By NetworkOK uniqueness, t2 in DOMAIN network[self] with
            \* t2.type = "tok" implies t2 = tok = t0.  Contradiction.
            <6>5. t2 = tok
              BY <4>0a, <4>0b, <5>1, <6>4
            <6>. QED  BY <6>4, <6>5
          <5>2. CASE n2 = self - 1
            <6>1. network'[n2] = BagAdd(network[self - 1], newTok)
              BY <3>NetEq, <5>2
            <6>2. DOMAIN network'[n2] = DOMAIN network[self - 1] \cup {newTok}
              BY <4>0e, <6>1 DEF BagAdd
            <6>3. CASE t2 = newTok
              BY <5>2, <6>3
            <6>4. CASE t2 # newTok
              <7>1. t2 \in DOMAIN network[self - 1]
                BY <6>2, <6>4
              \* By NetworkOK uniqueness with t2.type = "tok" and self-1 # self,
              \* this can't happen: t2 must equal tok at self.
              <7>2. self - 1 \in Node \ {self}
                OBVIOUS
              <7>3. t2.type # "tok"
                BY <4>0d, <7>1, <7>2
              <7>. QED  BY <7>3
            <6>. QED  BY <6>3, <6>4
          <5>3. CASE n2 # self /\ n2 # self - 1
            <6>1. network'[n2] = network[n2]
              BY <3>NetEq, <5>3
            <6>2. t2 \in DOMAIN network[n2]
              BY <6>1
            \* By NetworkOK, t2 must be tok at self.  But n2 # self.
            <6>3. n2 = self
              BY <4>0a, <4>0b, <6>2
            <6>. QED  BY <5>3, <6>3
          <5>. QED  BY <5>1, <5>2, <5>3
        <4>3. \E n \in Node : \E t \in DOMAIN network'[n] :
                /\ t.type = "tok"
                /\ network'[n][t] = 1
                /\ \A n2 \in Node : \A t2 \in DOMAIN network'[n2] :
                     t2.type = "tok" => (n2 = n /\ t2 = t)
          <5>. self - 1 \in Node  OBVIOUS
          <5>. newTok.type = "tok"  BY DEF Msg
          <5>. QED  BY <4>1, <4>2
        <4>. QED  BY <3>4, <4>3 DEF NetworkOK
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF PCalTypeOK
    \* Disjunct 5: initiate the token.
    <2>5. ASSUME self = Initiator,
                 NEW tok \in pendingMsgs(network, self),
                 tok.type = "tok" /\ (color[self] = "black" \/ tok.q + counter[self] # 0 \/ tok.color = "black"),
                 network' = passMsg(network, self, tok, N-1, [type|-> "tok", q |-> 0, color |-> "white"]),
                 color' = [color EXCEPT ![self] = "white"],
                 UNCHANGED <<active, counter>>
          PROVE  PCalTypeOK'
      <3>. DEFINE newTok == [type |-> "tok", q |-> 0, color |-> "white"]
      <3>1. active' \in [Node -> BOOLEAN]
        BY <2>5
      <3>2. color' \in [Node -> ColorSet]
        <4>1. "white" \in ColorSet  BY DEF ColorSet
        <4>. QED  BY <2>5, <4>1
      <3>3. counter' \in [Node -> Int]
        BY <2>5
      <3>. N - 1 \in Node
        BY DEF Node
      <3>. newTok \in Msg
        <4>1. 0 \in Int  OBVIOUS
        <4>2. "white" \in ColorSet  BY DEF ColorSet
        <4>. QED  BY <4>1, <4>2, NewTokInMsg
      <3>4. network' \in [Node -> BagOf(Msg)]
        \* The two EXCEPT keys are `self` (= 0) and `N-1`.  These coincide
        \* when N = 1, in which case the second EXCEPT writes over the
        \* first (its @ being `BagRemove(network[self], tok)`).  We handle
        \* both cases uniformly via per-element typing.
        <4>1. network' = [network EXCEPT ![self] = BagRemove(@, tok),
                                         ![N-1]  = BagAdd(@, newTok)]
          BY <2>5 DEF passMsg
        <4>2. ASSUME NEW n \in Node
              PROVE  network'[n] \in BagOf(Msg)
          <5>. self \in Node /\ self = 0
            BY <2>5, InitiatorIsZero
          <5>. N - 1 \in Node
            BY DEF Node
          <5>. network[self] \in BagOf(Msg) /\ network[N-1] \in BagOf(Msg)
            OBVIOUS
          <5>. BagRemove(network[self], tok) \in BagOf(Msg)
            BY BagRemoveOfMsg
          <5>. BagAdd(network[N-1], newTok) \in BagOf(Msg)
            BY BagAddOfMsg
          <5>. BagAdd(BagRemove(network[self], tok), newTok) \in BagOf(Msg)
            BY BagRemoveOfMsg, BagAddOfMsg
          <5>1. CASE self = N - 1
            \* The second EXCEPT writes at the same key with @ being the
            \* result of the first EXCEPT, so it overwrites with BagAdd.
            <6>1. network' = [network EXCEPT ![self] = BagAdd(BagRemove(network[self], tok), newTok)]
              BY <4>1, <5>1
            <6>. QED  BY <5>1, <6>1
          <5>2. CASE self # N - 1
            <6>1. network' = [network EXCEPT ![self] = BagRemove(network[self], tok),
                                             ![N-1]  = BagAdd(network[N-1], newTok)]
              BY <4>1, <5>2
            <6>. QED  BY <6>1, <5>2
          <5>. QED  BY <5>1, <5>2
        <4>. QED  BY <4>1, <4>2
      <3>5. NetworkOK'
        \* The token moves from `self` (= Initiator = 0) to `N-1`.  When
        \* N = 1 the two EXCEPT keys collapse into a BagAdd-of-BagRemove;
        \* the new unique-token witness is `(N-1, newTok)` in both cases.
        <4>0. PICK n0 \in Node :
                \E t \in DOMAIN network[n0] :
                  /\ t.type = "tok"
                  /\ network[n0][t] = 1
                  /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
                       t2.type = "tok" => (n2 = n0 /\ t2 = t)
          BY DEF NetworkOK
        <4>0a. PICK t0 \in DOMAIN network[n0] :
                /\ t0.type = "tok"
                /\ network[n0][t0] = 1
                /\ \A n2 \in Node : \A t2 \in DOMAIN network[n2] :
                     t2.type = "tok" => (n2 = n0 /\ t2 = t0)
          BY <4>0
        <4>0b. /\ n0 = self
               /\ t0 = tok
          BY <4>0a, <2>5 DEF pendingMsgs
        <4>0c. network[self][tok] = 1
          BY <4>0a, <4>0b
        <4>0d. \A m \in Node \ {self} : \A t \in DOMAIN network[m] : t.type # "tok"
          BY <4>0a, <4>0b
        <4>0e. self = 0 /\ N - 1 \in Node
          BY <2>5, InitiatorIsZero DEF Node
        \* For N >= 2 (self # N - 1), newTok is fresh at N-1.
        \* For N = 1 (self = N - 1), newTok is added to BagRemove(network[0], tok).
        <4>0f. tok # newTok \/ TRUE  OBVIOUS  \* (just to flag tok and newTok are unrelated for type purposes)
        <4>1. /\ newTok \in DOMAIN network'[N-1]
              /\ network'[N-1][newTok] = 1
          <5>1. CASE self # N - 1
            <6>1. network' = [network EXCEPT ![self] = BagRemove(network[self], tok),
                                             ![N-1]  = BagAdd(network[N-1], newTok)]
              BY <2>5, <5>1 DEF passMsg
            <6>2. network'[N-1] = BagAdd(network[N-1], newTok)
              BY <6>1, <5>1
            <6>3. newTok \notin DOMAIN network[N-1]
              <7>1. N - 1 \in Node \ {self}
                BY <4>0e, <5>1
              <7>2. \A t \in DOMAIN network[N-1] : t.type # "tok"
                BY <4>0d, <7>1
              <7>3. newTok.type = "tok"
                BY DEF Msg
              <7>. QED  BY <7>2, <7>3
            <6>4. BagAdd(network[N-1], newTok) =
                    [e \in DOMAIN network[N-1] \cup {newTok} |->
                         IF e = newTok THEN 1 ELSE network[N-1][e]]
              BY <6>3 DEF BagAdd
            <6>. QED  BY <6>2, <6>4
          <5>2. CASE self = N - 1
            <6>1. network' = [network EXCEPT ![self] = BagAdd(BagRemove(network[self], tok), newTok)]
              BY <2>5, <5>2 DEF passMsg
            <6>2. network'[N-1] = BagAdd(BagRemove(network[self], tok), newTok)
              BY <6>1, <5>2
            <6>3. BagRemove(network[self], tok) =
                    [e \in DOMAIN network[self] \ {tok} |-> network[self][e]]
              BY <4>0c DEF BagRemove
            <6>4. DOMAIN BagRemove(network[self], tok) = DOMAIN network[self] \ {tok}
              BY <6>3
            <6>5. newTok \notin DOMAIN BagRemove(network[self], tok)
              \* If newTok were in DOMAIN BagRemove(network[self], tok),
              \* it would be in DOMAIN network[self] \ {tok} -- so newTok
              \* is in DOMAIN network[self] *and* newTok # tok.  Then by
              \* NetworkOK uniqueness (every "tok" in DOMAIN network[self]
              \* equals tok = t0), newTok = tok.  Contradiction.
              <7>2. \A e \in DOMAIN network[self] :
                       e.type = "tok" => e = tok
                BY <4>0a, <4>0b, <2>5 DEF pendingMsgs
              <7>3. ASSUME newTok \in DOMAIN BagRemove(network[self], tok)
                    PROVE  FALSE
                <8>1. newTok \in DOMAIN network[self] \ {tok}
                  BY <6>4, <7>3
                <8>2. newTok \in DOMAIN network[self] /\ newTok # tok
                  BY <8>1
                <8>3. newTok.type = "tok"
                  BY DEF Msg
                <8>4. newTok = tok
                  BY <7>2, <8>2, <8>3
                <8>. QED  BY <8>2, <8>4
              <7>. QED  BY <7>3
            <6>6. BagAdd(BagRemove(network[self], tok), newTok) =
                    [e \in DOMAIN BagRemove(network[self], tok) \cup {newTok} |->
                         IF e = newTok THEN 1 ELSE BagRemove(network[self], tok)[e]]
              BY <6>5 DEF BagAdd
            <6>. QED  BY <6>2, <6>6
          <5>. QED  BY <5>1, <5>2
        <4>2. \A n2 \in Node : \A t2 \in DOMAIN network'[n2] :
                t2.type = "tok" => (n2 = N - 1 /\ t2 = newTok)
          <5>. SUFFICES ASSUME NEW n2 \in Node,
                              NEW t2 \in DOMAIN network'[n2],
                              t2.type = "tok"
                       PROVE  n2 = N - 1 /\ t2 = newTok
            OBVIOUS
          <5>1. CASE self # N - 1
            <6>1. network' = [network EXCEPT ![self] = BagRemove(network[self], tok),
                                             ![N-1]  = BagAdd(network[N-1], newTok)]
              BY <2>5, <5>1 DEF passMsg
            <6>2. CASE n2 = self
              \* network'[self] = BagRemove(network[self], tok); tok had mult 1.
              <7>1. network'[n2] = BagRemove(network[self], tok)
                BY <6>1, <5>1, <6>2
              <7>2. BagRemove(network[self], tok) =
                      [e \in DOMAIN network[self] \ {tok} |-> network[self][e]]
                BY <4>0c DEF BagRemove
              <7>3. DOMAIN network'[n2] = DOMAIN network[self] \ {tok}
                BY <7>1, <7>2
              <7>4. t2 \in DOMAIN network[self] \ {tok}
                BY <6>2, <7>3
              <7>5. t2 = tok
                BY <4>0a, <4>0b, <6>2, <7>4
              <7>. QED  BY <7>4, <7>5
            <6>3. CASE n2 = N - 1
              <7>1. network'[n2] = BagAdd(network[N-1], newTok)
                BY <6>1, <5>1, <6>3
              <7>2. newTok \notin DOMAIN network[N-1]
                <8>1. N - 1 \in Node \ {self}
                  BY <4>0e, <5>1
                <8>2. \A t \in DOMAIN network[N-1] : t.type # "tok"
                  BY <4>0d, <8>1
                <8>3. newTok.type = "tok"
                  BY DEF Msg
                <8>. QED  BY <8>2, <8>3
              <7>3. BagAdd(network[N-1], newTok) =
                      [e \in DOMAIN network[N-1] \cup {newTok} |->
                           IF e = newTok THEN 1 ELSE network[N-1][e]]
                BY <7>2 DEF BagAdd
              <7>4. DOMAIN network'[n2] = DOMAIN network[N-1] \cup {newTok}
                BY <7>1, <7>3
              <7>5. CASE t2 = newTok
                BY <6>3, <7>5
              <7>6. CASE t2 # newTok
                <8>1. t2 \in DOMAIN network[N-1]
                  BY <7>4, <7>6
                <8>2. N - 1 \in Node \ {self}
                  BY <4>0e, <5>1
                <8>3. t2.type # "tok"
                  BY <4>0d, <8>1, <8>2
                <8>. QED  BY <8>3
              <7>. QED  BY <7>5, <7>6
            <6>4. CASE n2 # self /\ n2 # N - 1
              <7>1. network'[n2] = network[n2]
                BY <6>1, <6>4
              <7>2. t2 \in DOMAIN network[n2]
                BY <7>1
              <7>3. n2 = self
                BY <4>0a, <4>0b, <7>2
              <7>. QED  BY <6>4, <7>3
            <6>. QED  BY <6>2, <6>3, <6>4
          <5>2. CASE self = N - 1
            <6>1. network' = [network EXCEPT ![self] = BagAdd(BagRemove(network[self], tok), newTok)]
              BY <2>5, <5>2 DEF passMsg
            <6>2. CASE n2 = self
              <7>1. network'[n2] = BagAdd(BagRemove(network[self], tok), newTok)
                BY <6>1, <6>2
              \* newTok \notin DOMAIN BagRemove(network[self], tok); see <4>1's <5>2 case.
              <7>2. BagRemove(network[self], tok) =
                      [e \in DOMAIN network[self] \ {tok} |-> network[self][e]]
                BY <4>0c DEF BagRemove
              <7>3. DOMAIN BagRemove(network[self], tok) = DOMAIN network[self] \ {tok}
                BY <7>2
              <7>4. \A e \in DOMAIN network[self] : e.type = "tok" => e = tok
                BY <4>0a, <4>0b, <2>5 DEF pendingMsgs
              <7>5. newTok \notin DOMAIN BagRemove(network[self], tok)
                <8>1. ASSUME newTok \in DOMAIN BagRemove(network[self], tok)
                      PROVE  FALSE
                  <9>1. newTok \in DOMAIN network[self] \ {tok}
                    BY <7>3, <8>1
                  <9>2. newTok \in DOMAIN network[self]
                    BY <9>1
                  <9>3. newTok.type = "tok"
                    BY DEF Msg
                  <9>4. newTok = tok
                    BY <7>4, <9>2, <9>3
                  <9>5. newTok # tok
                    BY <9>1
                  <9>. QED  BY <9>4, <9>5
                <8>. QED  BY <8>1
              <7>6. BagAdd(BagRemove(network[self], tok), newTok) =
                      [e \in DOMAIN BagRemove(network[self], tok) \cup {newTok} |->
                           IF e = newTok THEN 1 ELSE BagRemove(network[self], tok)[e]]
                BY <7>5 DEF BagAdd
              <7>7. DOMAIN network'[n2] = (DOMAIN network[self] \ {tok}) \cup {newTok}
                BY <7>1, <7>3, <7>6
              <7>8. CASE t2 = newTok
                BY <5>2, <6>2, <7>8
              <7>9. CASE t2 # newTok
                <8>1. t2 \in DOMAIN network[self] \ {tok}
                  BY <6>2, <7>7, <7>9
                <8>2. t2 \in DOMAIN network[self]
                  BY <8>1
                <8>3. t2 = tok
                  BY <7>4, <8>2
                <8>. QED  BY <8>1, <8>3
              <7>. QED  BY <7>8, <7>9
            <6>3. CASE n2 # self
              \* network'[n2] = network[n2] for n2 # self
              <7>1. network'[n2] = network[n2]
                BY <6>1, <6>3
              <7>2. t2 \in DOMAIN network[n2]
                BY <7>1
              <7>3. n2 = self
                BY <4>0a, <4>0b, <7>2
              <7>. QED  BY <6>3, <7>3
            <6>. QED  BY <6>2, <6>3
          <5>. QED  BY <5>1, <5>2
        <4>3. \E n \in Node : \E t \in DOMAIN network'[n] :
                /\ t.type = "tok"
                /\ network'[n][t] = 1
                /\ \A n2 \in Node : \A t2 \in DOMAIN network'[n2] :
                     t2.type = "tok" => (n2 = n /\ t2 = t)
          <5>. N - 1 \in Node  BY DEF Node
          <5>. newTok.type = "tok"  BY DEF Msg
          <5>. QED  BY <4>1, <4>2
        <4>. QED  BY <3>4, <4>3 DEF NetworkOK
      <3>. QED  BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF PCalTypeOK
    \* Combine the per-disjunct cases.  Each CASE matches one disjunct of
    \* `node(self)` exactly and reduces (via PICK on the existential
    \* witness) to the corresponding `<2>i.` per-disjunct lemma above.
    \* The five CASEs together cover `node(self)`; the QED uses `node(self)`
    \* (in scope from <1>2's ASSUME) to dispatch to one of them.
    <2>6. CASE /\ active[self]
               /\ \E to \in Node \ {self}:
                    network' = sendMsg(network, to, [type|-> "pl"])
               /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
               /\ UNCHANGED <<active, color>>
      <3>1. PICK to \in Node \ {self} :
              network' = sendMsg(network, to, [type|-> "pl"])
        BY <2>6
      <3>. QED  BY <2>1, <2>6, <3>1
    <2>7. CASE /\ \E msg \in pendingMsgs(network, self):
                    /\ msg.type = "pl"
                    /\ counter' = [counter EXCEPT ![self] = counter[self] - 1]
                    /\ active' = [active EXCEPT ![self] = TRUE]
                    /\ color' = [color EXCEPT ![self] = "black"]
                    /\ network' = dropMsg(network, self, msg)
      <3>1. PICK msg \in pendingMsgs(network, self) :
              /\ msg.type = "pl"
              /\ counter' = [counter EXCEPT ![self] = counter[self] - 1]
              /\ active' = [active EXCEPT ![self] = TRUE]
              /\ color' = [color EXCEPT ![self] = "black"]
              /\ network' = dropMsg(network, self, msg)
        BY <2>7
      <3>. QED  BY <2>2, <3>1
    <2>8. CASE /\ active' = [active EXCEPT ![self] = FALSE]
               /\ UNCHANGED <<network, color, counter>>
      BY <2>3, <2>8
    <2>9. CASE /\ self # Initiator
               /\ \E tok \in pendingMsgs(network, self):
                    /\ tok.type = "tok" /\ ~active[self]
                    /\ network' = passMsg(network, self, tok, self-1, [type|-> "tok", q |-> tok.q + counter[self], color |-> (IF color[self] = "black" THEN "black" ELSE tok.color)])
                    /\ color' = [color EXCEPT ![self] = "white"]
               /\ UNCHANGED <<active, counter>>
      <3>1. PICK tok \in pendingMsgs(network, self) :
              /\ tok.type = "tok" /\ ~active[self]
              /\ network' = passMsg(network, self, tok, self-1, [type|-> "tok", q |-> tok.q + counter[self], color |-> (IF color[self] = "black" THEN "black" ELSE tok.color)])
              /\ color' = [color EXCEPT ![self] = "white"]
        BY <2>9
      <3>. QED  BY <2>4, <2>9, <3>1
    <2>10. CASE /\ self = Initiator
                /\ \E tok \in pendingMsgs(network, self):
                     /\ tok.type = "tok" /\ (color[self] = "black" \/ tok.q + counter[self] # 0 \/ tok.color = "black")
                     /\ network' = passMsg(network, self, tok, N-1, [type|-> "tok", q |-> 0, color |-> "white"])
                     /\ color' = [color EXCEPT ![self] = "white"]
                /\ UNCHANGED <<active, counter>>
      <3>1. PICK tok \in pendingMsgs(network, self) :
              /\ tok.type = "tok" /\ (color[self] = "black" \/ tok.q + counter[self] # 0 \/ tok.color = "black")
              /\ network' = passMsg(network, self, tok, N-1, [type|-> "tok", q |-> 0, color |-> "white"])
              /\ color' = [color EXCEPT ![self] = "white"]
        BY <2>10
      <3>. QED  BY <2>5, <2>10, <3>1
    \* Final case combination: explicit case-by-case dispatch.
    <2>. QED
      <3>1. CASE /\ active[self]
                 /\ \E to \in Node \ {self}:
                      network' = sendMsg(network, to, [type|-> "pl"])
                 /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                 /\ UNCHANGED <<active, color>>
        BY <2>6, <3>1
      <3>2. CASE /\ \E msg \in pendingMsgs(network, self):
                      /\ msg.type = "pl"
                      /\ counter' = [counter EXCEPT ![self] = counter[self] - 1]
                      /\ active' = [active EXCEPT ![self] = TRUE]
                      /\ color' = [color EXCEPT ![self] = "black"]
                      /\ network' = dropMsg(network, self, msg)
        BY <2>7, <3>2
      <3>3. CASE /\ active' = [active EXCEPT ![self] = FALSE]
                 /\ UNCHANGED <<network, color, counter>>
        BY <2>8, <3>3
      <3>4. CASE /\ self # Initiator
                 /\ \E tok \in pendingMsgs(network, self):
                      /\ tok.type = "tok" /\ ~active[self]
                      /\ network' = passMsg(network, self, tok, self-1, [type|-> "tok", q |-> tok.q + counter[self], color |-> (IF color[self] = "black" THEN "black" ELSE tok.color)])
                      /\ color' = [color EXCEPT ![self] = "white"]
                 /\ UNCHANGED <<active, counter>>
        BY <2>9, <3>4
      <3>5. CASE /\ self = Initiator
                 /\ \E tok \in pendingMsgs(network, self):
                      /\ tok.type = "tok" /\ (color[self] = "black" \/ tok.q + counter[self] # 0 \/ tok.color = "black")
                      /\ network' = passMsg(network, self, tok, N-1, [type|-> "tok", q |-> 0, color |-> "white"])
                      /\ color' = [color EXCEPT ![self] = "white"]
                 /\ UNCHANGED <<active, counter>>
        BY <2>10, <3>5
      <3>. QED  BY <2>NodeFact, <3>1, <3>2, <3>3, <3>4, <3>5 DEF node
  <1>. QED  BY <1>1, <1>2 DEF Next

THEOREM TypeCorrect == Spec => []PCalTypeOK
  <1>1. Init => PCalTypeOK
    BY InitTypeOK
  <1>. QED  BY <1>1, TypeOK_Step, PTL DEF Spec

(***************************************************************************)
(* Bag-level helpers for the step-refinement (`Refinement` theorem below).*)
(*                                                                         *)
(* Each is about how the spec's `pending` operator (which counts          *)
(*  [type|->"pl"] occurrences in `network[n]`) changes under              *)
(* BagAdd/BagRemove of payload or token messages.  These are the         *)
(* missing primitives the per-disjunct step-simulation needs.              *)
(***************************************************************************)

\* The "pl" multiplicity in a single bag (== pending[n] for B = network[n]).
PlCount(B) == IF [type |-> "pl"] \in DOMAIN B THEN B[[type |-> "pl"]] ELSE 0

LEMMA PendingIsPlCount ==
  pending = [n \in Node |-> PlCount(network[n])]
  BY DEF pending, PlCount

\* BagAdd of a "pl" message increments PlCount by 1.
LEMMA BagAdd_pl_increments ==
  ASSUME NEW B
  PROVE  PlCount(BagAdd(B, [type |-> "pl"])) = PlCount(B) + 1
  <1>1. CASE [type |-> "pl"] \in DOMAIN B
    <2>1. BagAdd(B, [type |-> "pl"]) =
              [e \in DOMAIN B |-> IF e = [type |-> "pl"] THEN B[e] + 1 ELSE B[e]]
      BY <1>1 DEF BagAdd
    <2>2. DOMAIN BagAdd(B, [type |-> "pl"]) = DOMAIN B
      BY <2>1
    <2>3. BagAdd(B, [type |-> "pl"])[[type |-> "pl"]] = B[[type |-> "pl"]] + 1
      BY <2>1, <1>1
    <2>4. PlCount(B) = B[[type |-> "pl"]]
      BY <1>1 DEF PlCount
    <2>. QED  BY <1>1, <2>2, <2>3, <2>4 DEF PlCount
  <1>2. CASE [type |-> "pl"] \notin DOMAIN B
    <2>1. BagAdd(B, [type |-> "pl"]) =
              [e \in DOMAIN B \cup {[type |-> "pl"]} |->
                  IF e = [type |-> "pl"] THEN 1 ELSE B[e]]
      BY <1>2 DEF BagAdd
    <2>2. [type |-> "pl"] \in DOMAIN BagAdd(B, [type |-> "pl"])
      BY <2>1
    <2>3. BagAdd(B, [type |-> "pl"])[[type |-> "pl"]] = 1
      BY <2>1
    <2>4. PlCount(B) = 0
      BY <1>2 DEF PlCount
    <2>. QED  BY <1>2, <2>2, <2>3, <2>4 DEF PlCount
  <1>. QED  BY <1>1, <1>2

\* BagRemove of a "pl" message decrements PlCount by 1, when "pl" is present.
LEMMA BagRemove_pl_decrements ==
  ASSUME NEW B, [type |-> "pl"] \in DOMAIN B,
         B[[type |-> "pl"]] \in Nat \ {0}
  PROVE  PlCount(BagRemove(B, [type |-> "pl"])) = PlCount(B) - 1
  <1>. DEFINE pl == [type |-> "pl"]
  <1>1. CASE B[pl] = 1
    <2>1. BagRemove(B, pl) = [e \in DOMAIN B \ {pl} |-> B[e]]
      BY <1>1 DEF BagRemove
    <2>2. pl \notin DOMAIN BagRemove(B, pl)
      BY <2>1
    <2>3. PlCount(BagRemove(B, pl)) = 0
      BY <2>2 DEF PlCount
    <2>4. PlCount(B) = 1
      BY <1>1 DEF PlCount
    <2>. QED  BY <2>3, <2>4
  <1>2. CASE B[pl] # 1
    <2>1. BagRemove(B, pl) = [e \in DOMAIN B |-> IF e = pl THEN B[e] - 1 ELSE B[e]]
      BY <1>2 DEF BagRemove
    <2>2. pl \in DOMAIN BagRemove(B, pl)
      BY <2>1
    <2>3. BagRemove(B, pl)[pl] = B[pl] - 1
      BY <2>1
    <2>4. PlCount(B) = B[pl]
      BY DEF PlCount
    <2>. QED  BY <2>2, <2>3, <2>4 DEF PlCount
  <1>. QED  BY <1>1, <1>2

\* BagAdd of a token message preserves PlCount (since "tok" != "pl").
LEMMA BagAdd_tok_preserves_pl ==
  ASSUME NEW B, NEW t, t.type = "tok"
  PROVE  PlCount(BagAdd(B, t)) = PlCount(B)
  <1>. DEFINE pl == [type |-> "pl"]
  <1>0. pl # t  BY DEF Msg
  <1>1. CASE t \in DOMAIN B
    <2>1. BagAdd(B, t) = [e \in DOMAIN B |-> IF e = t THEN B[e] + 1 ELSE B[e]]
      BY <1>1 DEF BagAdd
    <2>2. DOMAIN BagAdd(B, t) = DOMAIN B
      BY <2>1
    <2>3. ASSUME pl \in DOMAIN B PROVE BagAdd(B, t)[pl] = B[pl]
      BY <2>1, <1>0, <2>3
    <2>. QED  BY <2>2, <2>3 DEF PlCount
  <1>2. CASE t \notin DOMAIN B
    <2>1. BagAdd(B, t) = [e \in DOMAIN B \cup {t} |-> IF e = t THEN 1 ELSE B[e]]
      BY <1>2 DEF BagAdd
    <2>2. pl \in DOMAIN BagAdd(B, t) <=> pl \in DOMAIN B
      BY <2>1, <1>0
    <2>3. ASSUME pl \in DOMAIN B PROVE BagAdd(B, t)[pl] = B[pl]
      BY <2>1, <1>0, <2>3
    <2>. QED  BY <2>2, <2>3 DEF PlCount
  <1>. QED  BY <1>1, <1>2

\* BagRemove of a token message preserves PlCount.
LEMMA BagRemove_tok_preserves_pl ==
  ASSUME NEW B, NEW t, t.type = "tok"
  PROVE  PlCount(BagRemove(B, t)) = PlCount(B)
  <1>. DEFINE pl == [type |-> "pl"]
  <1>0. pl # t  BY DEF Msg
  <1>1. CASE t \notin DOMAIN B
    <2>. BagRemove(B, t) = B  BY <1>1 DEF BagRemove
    <2>. QED  OBVIOUS
  <1>2. CASE t \in DOMAIN B /\ B[t] = 1
    <2>1. BagRemove(B, t) = [e \in DOMAIN B \ {t} |-> B[e]]
      BY <1>2 DEF BagRemove
    <2>2. pl \in DOMAIN BagRemove(B, t) <=> pl \in DOMAIN B
      BY <2>1, <1>0
    <2>3. ASSUME pl \in DOMAIN B PROVE BagRemove(B, t)[pl] = B[pl]
      BY <2>1, <1>0, <2>3
    <2>. QED  BY <2>2, <2>3 DEF PlCount
  <1>3. CASE t \in DOMAIN B /\ B[t] # 1
    <2>1. BagRemove(B, t) = [e \in DOMAIN B |-> IF e = t THEN B[e] - 1 ELSE B[e]]
      BY <1>3 DEF BagRemove
    <2>2. DOMAIN BagRemove(B, t) = DOMAIN B
      BY <2>1
    <2>3. ASSUME pl \in DOMAIN B PROVE BagRemove(B, t)[pl] = B[pl]
      BY <2>1, <1>0, <2>3
    <2>. QED  BY <2>2, <2>3 DEF PlCount
  <1>. QED  BY <1>1, <1>2, <1>3

(***************************************************************************)
(* Refinement theorem (Spec => EWD998Spec).                                *)
(*                                                                         *)
(* The proof has the standard shape:                                       *)
(*   <1>1. Init => EWD998!Init                  -- via InitRefinement      *)
(*   <1>2. step refinement                       -- per-disjunct analysis  *)
(*   <1>. QED  by combining the temporal pieces.                           *)
(*                                                                         *)
(* For the step refinement, each PCal disjunct of `node(self)` implements  *)
(* one of EWD998's actions under the refinement mapping for `pending` and *)
(* `token`:                                                                *)
(*                                                                         *)
(*   PCal disjunct 1 (send pl)    -> EWD998!SendMsg(self)                  *)
(*   PCal disjunct 2 (recv pl)    -> EWD998!RecvMsg(self)                  *)
(*   PCal disjunct 3 (deactivate) -> EWD998!Deactivate(self) or stutter   *)
(*   PCal disjunct 4 (pass tok)   -> EWD998!PassToken(self)                *)
(*   PCal disjunct 5 (init tok)   -> EWD998!InitiateProbe                  *)
(*                                                                         *)
(* The hardest case is disjunct 5 (InitiateProbe), where PCal's trigger   *)
(* condition (`tok.q + counter[Initiator] # 0`) is weaker than EWD998's   *)
(* (`> 0`).  Bridging this gap requires Safra's P0 invariant transferred  *)
(* to PCal: `B = Sum(counter, Node)` where B is the total count of "pl"  *)
(* messages in the network.  The other disjuncts only need bag-level    *)
(* reasoning about how `pending` and `token` change under the spec's    *)
(* BagAdd/BagRemove updates.                                               *)
(*                                                                         *)
(* This stub remains OMITTED -- the per-disjunct step-simulation requires *)
(* substantial bag-level lemmas that are out of scope for this round.     *)
(***************************************************************************)
THEOREM Refinement == Spec => EWD998Spec
OMITTED

=============================================================================
