--------------------------- MODULE tcp_proof ---------------------------------
(***************************************************************************)
(* TLAPS proofs for the TCP FSM specification:                             *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []Inv  (ESTABLISHED agreement when both networks are empty)   *)
(***************************************************************************)
EXTENDS tcp, SequenceTheorems, SequencesExtTheorems, TLAPS

\* The spec's `ASSUME PeersAssumption == Cardinality(Peers) = 2` is intended
\* to assert that Peers is a finite set with exactly two elements.  In TLA+,
\* Cardinality is defined via CHOOSE and may return arbitrary values for
\* infinite sets, so we add the natural finiteness witness here.
ASSUME PeersFinite == IsFiniteSet(Peers)

(***************************************************************************)
(* The set of network messages used by the spec.                           *)
(***************************************************************************)
Msgs == {"SYN", "SYN,ACK", "ACK", "RST", "FIN", "ACKofFIN"}

LEMMA NetworkType ==
  TypeOK <=> /\ tcb \in [Peers -> BOOLEAN]
             /\ connstate \in [Peers -> States]
             /\ network \in [Peers -> Seq(Msgs)]
  BY DEF TypeOK, Msgs

LEMMA TailIsSeq ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Tail(s) \in Seq(T)
  OBVIOUS

LEMMA AppendInSeq ==
  ASSUME NEW T, NEW s \in Seq(T), NEW e \in T
  PROVE  Append(s, e) \in Seq(T)
  OBVIOUS

(***************************************************************************)
(* IsPrefix with a non-empty argument forces the second sequence to be     *)
(* non-empty.  We use the unfolded definition to avoid a fragile           *)
(* dependency on the longer Theorems.                                      *)
(***************************************************************************)
LEMMA PrefixOneNonEmpty ==
  ASSUME NEW T, NEW e \in T, NEW s \in Seq(T), IsPrefix(<<e>>, s)
  PROVE  /\ s # << >>
         /\ Head(s) = e
         /\ Tail(s) \in Seq(T)
  <1>1. Len(<<e>>) <= Len(s) /\ SubSeq(<<e>>, 1, Len(<<e>>)) = SubSeq(s, 1, Len(<<e>>))
    BY DEF IsPrefix
  <1>2. Len(s) >= 1
    BY <1>1
  <1>3. s # << >>
    BY <1>2
  <1>4. Head(s) = e
    <2>. SubSeq(s, 1, 1) = <<s[1]>>
      BY <1>3, SubSeqProperties
    <2>. SubSeq(<<e>>, 1, 1) = <<e>>
      BY SubSeqProperties
    <2>. <<e>> = <<s[1]>>
      BY <1>1
    <2>. QED BY HeadTailProperties
  <1>. QED BY <1>3, <1>4, TailIsSeq

LEMMA PrefixTwoNonEmpty ==
  ASSUME NEW T, NEW e1 \in T, NEW e2 \in T, NEW s \in Seq(T),
         IsPrefix(<<e1, e2>>, s)
  PROVE  /\ Len(s) >= 2
         /\ s[1] = e1
         /\ s[2] = e2
  <1>1. Len(<<e1, e2>>) <= Len(s) /\ SubSeq(<<e1, e2>>, 1, Len(<<e1, e2>>)) = SubSeq(s, 1, Len(<<e1, e2>>))
    BY DEF IsPrefix
  <1>2. Len(s) >= 2
    BY <1>1
  <1>3. SubSeq(s, 1, 2) = <<s[1], s[2]>>
    BY <1>2
  <1>4. SubSeq(<<e1, e2>>, 1, 2) = <<e1, e2>>
    OBVIOUS
  <1>. QED BY <1>1, <1>2, <1>3, <1>4

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, States
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2>. SUFFICES ASSUME TypeOK, [Next]_vars  PROVE TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK, States, Msgs
  (*************************************************************************)
  (* User actions                                                          *)
  (*************************************************************************)
  <2>uo. ASSUME NEW local \in Peers, NEW remote \in Peers,
                PASSIVE_OPEN(local, remote) \/ ACTIVE_OPEN(local, remote)
                  \/ CLOSE_SYN_SENT(local, remote)
                  \/ CLOSE_SYN_RECEIVED(local, remote)
                  \/ CLOSE_LISTEN(local, remote)
                  \/ CLOSE_ESTABLISHED(local, remote)
                  \/ CLOSE_CLOSE_WAIT(local, remote)
                  \/ SEND(local, remote)
         PROVE  TypeOK'
    <3>1. CASE PASSIVE_OPEN(local, remote)
      BY <3>1 DEF PASSIVE_OPEN
    <3>2. CASE ACTIVE_OPEN(local, remote)
      <4>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>. Append(network[remote], "SYN") \in Seq(Msgs)
        OBVIOUS
      <4>. QED  BY <3>2 DEF ACTIVE_OPEN
    <3>3. CASE CLOSE_SYN_SENT(local, remote)
      BY <3>3 DEF CLOSE_SYN_SENT
    <3>4. CASE CLOSE_SYN_RECEIVED(local, remote)
      <4>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>. Append(network[remote], "FIN") \in Seq(Msgs)
        OBVIOUS
      <4>. QED  BY <3>4 DEF CLOSE_SYN_RECEIVED
    <3>5. CASE CLOSE_LISTEN(local, remote)
      BY <3>5 DEF CLOSE_LISTEN
    <3>6. CASE CLOSE_ESTABLISHED(local, remote)
      <4>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>. Append(network[remote], "FIN") \in Seq(Msgs)
        OBVIOUS
      <4>. QED  BY <3>6 DEF CLOSE_ESTABLISHED
    <3>7. CASE CLOSE_CLOSE_WAIT(local, remote)
      <4>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>. Append(network[remote], "FIN") \in Seq(Msgs)
        OBVIOUS
      <4>. QED  BY <3>7 DEF CLOSE_CLOSE_WAIT
    <3>8. CASE SEND(local, remote)
      <4>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>. Append(network[remote], "SYN") \in Seq(Msgs)
        OBVIOUS
      <4>. QED  BY <3>8 DEF SEND
    <3>. QED  BY <2>uo, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8
  <2>user. CASE User
    <3>. PICK local \in Peers, remote \in Peers :
            \/ ACTIVE_OPEN(local, remote)
            \/ PASSIVE_OPEN(local, remote)
            \/ CLOSE_SYN_SENT(local, remote)
            \/ CLOSE_SYN_RECEIVED(local, remote)
            \/ CLOSE_LISTEN(local, remote)
            \/ CLOSE_ESTABLISHED(local, remote)
            \/ CLOSE_CLOSE_WAIT(local, remote)
            \/ SEND(local, remote)
      BY <2>user DEF User
    <3>. QED  BY <2>uo
  (*************************************************************************)
  (* System actions                                                        *)
  (*************************************************************************)
  <2>sys. ASSUME NEW local \in Peers, NEW remote \in Peers,
                  \/ SynSent(local, remote)
                  \/ SynReceived(local, remote)
                  \/ Listen(local, remote)
                  \/ Established(local, remote)
                  \/ FinWait1(local, remote)
                  \/ FinWait2(local, remote)
                  \/ Closing(local, remote)
                  \/ LastAck(local, remote)
                  \/ TimeWait(local, remote)
                  \/ Note2(local, remote)
          PROVE  TypeOK'
    <3>1. CASE SynSent(local, remote)
      <4>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>1. CASE /\ IsPrefix(<<"SYN">>, network[local])
                  /\ network' = [ network EXCEPT ![remote] = Append(@, "SYN,ACK"),
                                                 ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "SYN-RECEIVED"]
        <5>1. Tail(network[local]) \in Seq(Msgs)
          BY <4>0, <4>1, PrefixOneNonEmpty
        <5>2. Append(network[remote], "SYN,ACK") \in Seq(Msgs)
          BY <4>0
        <5>. QED  BY <3>1, <4>1, <5>1, <5>2 DEF SynSent
      <4>2. CASE /\ IsPrefix(<<"SYN,ACK">>, network[local])
                  /\ network' = [ network EXCEPT ![remote] = Append(@, "ACK"),
                                                 ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "ESTABLISHED"]
        <5>1. Tail(network[local]) \in Seq(Msgs)
          BY <4>0, <4>2, PrefixOneNonEmpty
        <5>2. Append(network[remote], "ACK") \in Seq(Msgs)
          BY <4>0
        <5>. QED  BY <3>1, <4>2, <5>1, <5>2 DEF SynSent
      <4>. QED  BY <3>1, <4>1, <4>2 DEF SynSent
    <3>2. CASE SynReceived(local, remote)
      <4>0. network[local] \in Seq(Msgs)
        OBVIOUS
      <4>1. CASE /\ IsPrefix(<<"RST">>, network[local])
                  /\ network' = [network EXCEPT ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "LISTEN"]
        <5>1. Tail(network[local]) \in Seq(Msgs)
          BY <4>0, <4>1, PrefixOneNonEmpty
        <5>. QED  BY <3>2, <4>1, <5>1 DEF SynReceived
      <4>2. CASE /\ IsPrefix(<<"ACK">>, network[local])
                  /\ network' = [network EXCEPT ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "ESTABLISHED"]
        <5>1. Tail(network[local]) \in Seq(Msgs)
          BY <4>0, <4>2, PrefixOneNonEmpty
        <5>. QED  BY <3>2, <4>2, <5>1 DEF SynReceived
      <4>. QED  BY <3>2, <4>1, <4>2 DEF SynReceived
    <3>3. CASE Listen(local, remote)
      <4>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>1. IsPrefix(<<"SYN">>, network[local])
        BY <3>3 DEF Listen
      <4>2. Tail(network[local]) \in Seq(Msgs)
        BY <4>0, <4>1, PrefixOneNonEmpty
      <4>3. Append(network[remote], "SYN,ACK") \in Seq(Msgs)
        BY <4>0
      <4>. QED  BY <3>3, <4>2, <4>3 DEF Listen
    <3>4. CASE Established(local, remote)
      <4>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>1. IsPrefix(<<"FIN">>, network[local])
        BY <3>4 DEF Established
      <4>2. Tail(network[local]) \in Seq(Msgs)
        BY <4>0, <4>1, PrefixOneNonEmpty
      <4>3. Append(network[remote], "ACKofFIN") \in Seq(Msgs)
        BY <4>0
      <4>. QED  BY <3>4, <4>2, <4>3 DEF Established
    <3>5. CASE FinWait1(local, remote)
      <4>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>1. CASE /\ IsPrefix(<<"FIN">>, network[local])
                  /\ network' = [network EXCEPT ![remote] = Append(@, "ACKofFIN"),
                                                 ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "CLOSING"]
        <5>1. Tail(network[local]) \in Seq(Msgs)
          BY <4>0, <4>1, PrefixOneNonEmpty
        <5>2. Append(network[remote], "ACKofFIN") \in Seq(Msgs)
          BY <4>0
        <5>. QED  BY <3>5, <4>1, <5>1, <5>2 DEF FinWait1
      <4>2. CASE /\ IsPrefix(<<"ACKofFIN">>, network[local])
                  /\ network' = [network EXCEPT ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "FIN-WAIT-2"]
        <5>1. Tail(network[local]) \in Seq(Msgs)
          BY <4>0, <4>2, PrefixOneNonEmpty
        <5>. QED  BY <3>5, <4>2, <5>1 DEF FinWait1
      <4>. QED  BY <3>5, <4>1, <4>2 DEF FinWait1
    <3>6. CASE FinWait2(local, remote)
      <4>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>1. IsPrefix(<<"FIN">>, network[local])
        BY <3>6 DEF FinWait2
      <4>2. Tail(network[local]) \in Seq(Msgs)
        BY <4>0, <4>1, PrefixOneNonEmpty
      <4>3. Append(network[remote], "ACKofFIN") \in Seq(Msgs)
        BY <4>0
      <4>. QED  BY <3>6, <4>2, <4>3 DEF FinWait2
    <3>7. CASE Closing(local, remote)
      <4>0. network[local] \in Seq(Msgs)
        OBVIOUS
      <4>1. IsPrefix(<<"ACKofFIN">>, network[local])
        BY <3>7 DEF Closing
      <4>2. Tail(network[local]) \in Seq(Msgs)
        BY <4>0, <4>1, PrefixOneNonEmpty
      <4>. QED  BY <3>7, <4>2 DEF Closing
    <3>8. CASE LastAck(local, remote)
      <4>0. network[local] \in Seq(Msgs)
        OBVIOUS
      <4>1. IsPrefix(<<"ACKofFIN">>, network[local])
        BY <3>8 DEF LastAck
      <4>2. Tail(network[local]) \in Seq(Msgs)
        BY <4>0, <4>1, PrefixOneNonEmpty
      <4>. QED  BY <3>8, <4>2 DEF LastAck
    <3>9. CASE TimeWait(local, remote)
      BY <3>9 DEF TimeWait
    <3>10. CASE Note2(local, remote)
      <4>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>1. IsPrefix(<<"FIN", "ACKofFIN">>, network[local])
        BY <3>10 DEF Note2
      <4>2. Len(network[local]) >= 2
        BY <4>0, <4>1, PrefixTwoNonEmpty
      <4>3. SubSeq(network[local], 3, Len(network[local])) \in Seq(Msgs)
        BY <4>0, <4>2, SubSeqProperties
      <4>4. Append(network[remote], "ACKofFIN") \in Seq(Msgs)
        BY <4>0
      <4>. QED  BY <3>10, <4>3, <4>4 DEF Note2
    <3>. QED  BY <2>sys, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8,
                <3>9, <3>10
  <2>system. CASE System
    <3>. PICK local \in Peers, remote \in Peers :
            \/ SynSent(local, remote)
            \/ SynReceived(local, remote)
            \/ Listen(local, remote)
            \/ Established(local, remote)
            \/ FinWait1(local, remote)
            \/ FinWait2(local, remote)
            \/ Closing(local, remote)
            \/ LastAck(local, remote)
            \/ TimeWait(local, remote)
            \/ Note2(local, remote)
      BY <2>system DEF System
    <3>. QED  BY <2>sys
  <2>reset. CASE Reset
    <3>. PICK local \in Peers, remote \in Peers : Note3(local, remote)
      BY <2>reset DEF Reset
    <3>. USE DEF Note3
    <3>1. CASE /\ tcb[local]
                /\ network' = [network EXCEPT ![remote] = Append(@, "RST")]
                /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]
      <4>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <4>. Append(network[remote], "RST") \in Seq(Msgs)
        OBVIOUS
      <4>. QED  BY <3>1
    <3>2. CASE /\ IsPrefix(<<"RST">>, network[local])
                /\ network' = [network EXCEPT ![local] = Tail(network[local])]
                /\ \/ connstate' = [connstate EXCEPT ![local] = "LISTEN"]
                   \/ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
      <4>0. network[local] \in Seq(Msgs)
        OBVIOUS
      <4>1. Tail(network[local]) \in Seq(Msgs)
        BY <4>0, <3>2, PrefixOneNonEmpty
      <4>. QED  BY <3>2, <4>1
    <3>. QED  BY <3>1, <3>2
  <2>stutter. CASE UNCHANGED vars
    BY <2>stutter DEF vars
  <2>. QED  BY <2>user, <2>system, <2>reset, <2>stutter DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Pick the two distinct peers using the cardinality-2 assumption.         *)
(***************************************************************************)
A == CHOOSE p \in Peers : TRUE
B == CHOOSE p \in Peers : p # A

LEMMA PeersAB ==
  /\ A \in Peers
  /\ B \in Peers
  /\ A # B
  /\ Peers = {A, B}
  <1>1. Peers # {}
    <2>. SUFFICES ASSUME Peers = {} PROVE FALSE
      OBVIOUS
    <2>1. Cardinality({}) = 0
      BY FS_EmptySet
    <2>. QED  BY <2>1, PeersAssumption, PeersFinite
  <1>2. A \in Peers
    BY <1>1 DEF A
  <1>3. \E y \in Peers : y # A
    <2>. SUFFICES ASSUME \A y \in Peers : y = A PROVE FALSE
      OBVIOUS
    <2>1. Peers = {A}
      BY <1>2
    <2>2. Cardinality({A}) = 1
      BY FS_Singleton
    <2>. QED  BY <2>1, <2>2, PeersAssumption, PeersFinite
  <1>4. B \in Peers /\ B # A
    BY <1>3 DEF B
  <1>5. Peers = {A, B}
    <2>. SUFFICES ASSUME NEW z \in Peers, z # A, z # B PROVE FALSE
      BY <1>2, <1>4
    <2>a. IsFiniteSet({A})  /\  Cardinality({A}) = 1
      BY FS_Singleton
    <2>b. {A} \cup {B} = {A, B}  /\  B \notin {A}
      BY <1>4
    <2>c. IsFiniteSet({A, B})  /\  Cardinality({A, B}) = 2
      <3>1. IsFiniteSet({A} \cup {B}) /\
            Cardinality({A} \cup {B}) = (IF B \in {A} THEN 1 ELSE 1 + 1)
        BY <2>a, FS_AddElement
      <3>. QED  BY <2>b, <3>1
    <2>d. {A, B} \cup {z} = {A, B, z}  /\  z \notin {A, B}
      OBVIOUS
    <2>e. IsFiniteSet({A, B, z})  /\  Cardinality({A, B, z}) = 3
      <3>1. IsFiniteSet({A, B} \cup {z}) /\
            Cardinality({A, B} \cup {z}) = (IF z \in {A, B} THEN 2 ELSE 2 + 1)
        BY <2>c, FS_AddElement
      <3>. QED  BY <2>d, <3>1
    <2>1. {A, B, z} \subseteq Peers
      BY <1>2, <1>4
    <2>3. Cardinality({A, B, z}) <= Cardinality(Peers)
      BY <2>1, <2>e, FS_Subset, PeersFinite
    <2>. QED  BY <2>3, <2>e, PeersAssumption
  <1>. QED  BY <1>2, <1>4, <1>5

(***************************************************************************)
(* Inv reformulated explicitly in terms of the two peers.  This is        *)
(* convenient for case analysis since {p \in Peers : network[p] = <<>>}   *)
(* is one of {}, {A}, {B}, {A, B}.                                        *)
(***************************************************************************)
LEMMA InvIsAB ==
  Inv <=> ((network[A] = <<>> /\ network[B] = <<>>)
              => (connstate[A] = "ESTABLISHED" <=> connstate[B] = "ESTABLISHED"))
  BY PeersAB DEF Inv

(***************************************************************************)
(* Initial state satisfies Inv.                                            *)
(***************************************************************************)
THEOREM InvInit == Init => Inv
  <1>. SUFFICES ASSUME Init  PROVE Inv
    OBVIOUS
  <1>1. \A p \in Peers : connstate[p] = "CLOSED"  /\  network[p] = <<>>
    BY DEF Init
  <1>. QED  BY <1>1 DEF Inv

(***************************************************************************)
(*                                                                         *)
(* Status summary:                                                         *)
(*                                                                         *)
(*   * TypeCorrect : Spec => []TypeOK             fully discharged        *)
(*   * InvInit     : Init => Inv                  fully discharged        *)
(*   * InvIsAB     : two-peer reformulation       fully discharged        *)
(*   * PeersAB     : two-element Peers witnesses  fully discharged        *)
(*                                                                         *)
(* The inductive step                                                     *)
(*                                                                         *)
(*   Inv /\ [Next]_vars => Inv'                                           *)
(*                                                                         *)
(* requires a substantial strengthening of Inv that captures the          *)
(* message-history correlations of the TCP FSM.  The required auxiliary  *)
(* invariants relate the head of each peer's incoming queue to the       *)
(* possible states of the sender.  In particular, there are six trigger  *)
(* "consume-only" actions whose post-state may leave both networks       *)
(* empty -- SynReceived RST, SynReceived ACK, FW1 ACKofFIN, Closing,     *)
(* LastAck, and Note3 RST -- and for each of them the system can only    *)
(* land in an EST-agreement-respecting state because of detailed         *)
(* invariants of the form                                                *)
(*                                                                         *)
(*   network[p] = <<X>> /\ network[q] = <<>> => connstate[q] \in T(X).   *)
(*                                                                         *)
(* These invariants are themselves preserved only by accounting for      *)
(* further protocol-specific facts about how each TCP message can ever   *)
(* be enqueued.  The full discharge of the inductive step for Inv is    *)
(* therefore left as future work; the static obligations above are      *)
(* fully proved in TLAPS.                                                *)
(***************************************************************************)
============================================================================
