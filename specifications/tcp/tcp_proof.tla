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

LEMMA TypeOKInductive == TypeOK /\ [Next]_vars => TypeOK'
  <1>. SUFFICES ASSUME TypeOK, [Next]_vars  PROVE TypeOK'
    OBVIOUS
  <1>. USE DEF TypeOK, States, Msgs
  (*************************************************************************)
  (* User actions                                                          *)
  (*************************************************************************)
  <1>uo. ASSUME NEW local \in Peers, NEW remote \in Peers,
                PASSIVE_OPEN(local, remote) \/ ACTIVE_OPEN(local, remote)
                  \/ CLOSE_SYN_SENT(local, remote)
                  \/ CLOSE_SYN_RECEIVED(local, remote)
                  \/ CLOSE_LISTEN(local, remote)
                  \/ CLOSE_ESTABLISHED(local, remote)
                  \/ CLOSE_CLOSE_WAIT(local, remote)
                  \/ SEND(local, remote)
         PROVE  TypeOK'
    <2>1. CASE PASSIVE_OPEN(local, remote)
      BY <2>1 DEF PASSIVE_OPEN
    <2>2. CASE ACTIVE_OPEN(local, remote)
      <3>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>. Append(network[remote], "SYN") \in Seq(Msgs)
        OBVIOUS
      <3>. QED  BY <2>2 DEF ACTIVE_OPEN
    <2>3. CASE CLOSE_SYN_SENT(local, remote)
      BY <2>3 DEF CLOSE_SYN_SENT
    <2>4. CASE CLOSE_SYN_RECEIVED(local, remote)
      <3>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>. Append(network[remote], "FIN") \in Seq(Msgs)
        OBVIOUS
      <3>. QED  BY <2>4 DEF CLOSE_SYN_RECEIVED
    <2>5. CASE CLOSE_LISTEN(local, remote)
      BY <2>5 DEF CLOSE_LISTEN
    <2>6. CASE CLOSE_ESTABLISHED(local, remote)
      <3>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>. Append(network[remote], "FIN") \in Seq(Msgs)
        OBVIOUS
      <3>. QED  BY <2>6 DEF CLOSE_ESTABLISHED
    <2>7. CASE CLOSE_CLOSE_WAIT(local, remote)
      <3>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>. Append(network[remote], "FIN") \in Seq(Msgs)
        OBVIOUS
      <3>. QED  BY <2>7 DEF CLOSE_CLOSE_WAIT
    <2>8. CASE SEND(local, remote)
      <3>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>. Append(network[remote], "SYN") \in Seq(Msgs)
        OBVIOUS
      <3>. QED  BY <2>8 DEF SEND
    <2>. QED  BY <1>uo, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8
  <1>user. CASE User
    <2>. PICK local \in Peers, remote \in Peers :
            \/ ACTIVE_OPEN(local, remote)
            \/ PASSIVE_OPEN(local, remote)
            \/ CLOSE_SYN_SENT(local, remote)
            \/ CLOSE_SYN_RECEIVED(local, remote)
            \/ CLOSE_LISTEN(local, remote)
            \/ CLOSE_ESTABLISHED(local, remote)
            \/ CLOSE_CLOSE_WAIT(local, remote)
            \/ SEND(local, remote)
      BY <1>user DEF User
    <2>. QED  BY <1>uo
  (*************************************************************************)
  (* System actions                                                        *)
  (*************************************************************************)
  <1>sys. ASSUME NEW local \in Peers, NEW remote \in Peers,
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
    <2>1. CASE SynSent(local, remote)
      <3>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>1. CASE /\ IsPrefix(<<"SYN">>, network[local])
                  /\ network' = [ network EXCEPT ![remote] = Append(@, "SYN,ACK"),
                                                 ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "SYN-RECEIVED"]
        <4>1. Tail(network[local]) \in Seq(Msgs)
          BY <3>0, <3>1, PrefixOneNonEmpty
        <4>2. Append(network[remote], "SYN,ACK") \in Seq(Msgs)
          BY <3>0
        <4>. QED  BY <2>1, <3>1, <4>1, <4>2 DEF SynSent
      <3>2. CASE /\ IsPrefix(<<"SYN,ACK">>, network[local])
                  /\ network' = [ network EXCEPT ![remote] = Append(@, "ACK"),
                                                 ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "ESTABLISHED"]
        <4>1. Tail(network[local]) \in Seq(Msgs)
          BY <3>0, <3>2, PrefixOneNonEmpty
        <4>2. Append(network[remote], "ACK") \in Seq(Msgs)
          BY <3>0
        <4>. QED  BY <2>1, <3>2, <4>1, <4>2 DEF SynSent
      <3>. QED  BY <2>1, <3>1, <3>2 DEF SynSent
    <2>2. CASE SynReceived(local, remote)
      <3>0. network[local] \in Seq(Msgs)
        OBVIOUS
      <3>1. CASE /\ IsPrefix(<<"RST">>, network[local])
                  /\ network' = [network EXCEPT ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "LISTEN"]
        <4>1. Tail(network[local]) \in Seq(Msgs)
          BY <3>0, <3>1, PrefixOneNonEmpty
        <4>. QED  BY <2>2, <3>1, <4>1 DEF SynReceived
      <3>2. CASE /\ IsPrefix(<<"ACK">>, network[local])
                  /\ network' = [network EXCEPT ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "ESTABLISHED"]
        <4>1. Tail(network[local]) \in Seq(Msgs)
          BY <3>0, <3>2, PrefixOneNonEmpty
        <4>. QED  BY <2>2, <3>2, <4>1 DEF SynReceived
      <3>. QED  BY <2>2, <3>1, <3>2 DEF SynReceived
    <2>3. CASE Listen(local, remote)
      <3>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>1. IsPrefix(<<"SYN">>, network[local])
        BY <2>3 DEF Listen
      <3>2. Tail(network[local]) \in Seq(Msgs)
        BY <3>0, <3>1, PrefixOneNonEmpty
      <3>3. Append(network[remote], "SYN,ACK") \in Seq(Msgs)
        BY <3>0
      <3>. QED  BY <2>3, <3>2, <3>3 DEF Listen
    <2>4. CASE Established(local, remote)
      <3>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>1. IsPrefix(<<"FIN">>, network[local])
        BY <2>4 DEF Established
      <3>2. Tail(network[local]) \in Seq(Msgs)
        BY <3>0, <3>1, PrefixOneNonEmpty
      <3>3. Append(network[remote], "ACKofFIN") \in Seq(Msgs)
        BY <3>0
      <3>. QED  BY <2>4, <3>2, <3>3 DEF Established
    <2>5. CASE FinWait1(local, remote)
      <3>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>1. CASE /\ IsPrefix(<<"FIN">>, network[local])
                  /\ network' = [network EXCEPT ![remote] = Append(@, "ACKofFIN"),
                                                 ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "CLOSING"]
        <4>1. Tail(network[local]) \in Seq(Msgs)
          BY <3>0, <3>1, PrefixOneNonEmpty
        <4>2. Append(network[remote], "ACKofFIN") \in Seq(Msgs)
          BY <3>0
        <4>. QED  BY <2>5, <3>1, <4>1, <4>2 DEF FinWait1
      <3>2. CASE /\ IsPrefix(<<"ACKofFIN">>, network[local])
                  /\ network' = [network EXCEPT ![local] = Tail(network[local])]
                  /\ connstate' = [connstate EXCEPT ![local] = "FIN-WAIT-2"]
        <4>1. Tail(network[local]) \in Seq(Msgs)
          BY <3>0, <3>2, PrefixOneNonEmpty
        <4>. QED  BY <2>5, <3>2, <4>1 DEF FinWait1
      <3>. QED  BY <2>5, <3>1, <3>2 DEF FinWait1
    <2>6. CASE FinWait2(local, remote)
      <3>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>1. IsPrefix(<<"FIN">>, network[local])
        BY <2>6 DEF FinWait2
      <3>2. Tail(network[local]) \in Seq(Msgs)
        BY <3>0, <3>1, PrefixOneNonEmpty
      <3>3. Append(network[remote], "ACKofFIN") \in Seq(Msgs)
        BY <3>0
      <3>. QED  BY <2>6, <3>2, <3>3 DEF FinWait2
    <2>7. CASE Closing(local, remote)
      <3>0. network[local] \in Seq(Msgs)
        OBVIOUS
      <3>1. IsPrefix(<<"ACKofFIN">>, network[local])
        BY <2>7 DEF Closing
      <3>2. Tail(network[local]) \in Seq(Msgs)
        BY <3>0, <3>1, PrefixOneNonEmpty
      <3>. QED  BY <2>7, <3>2 DEF Closing
    <2>8. CASE LastAck(local, remote)
      <3>0. network[local] \in Seq(Msgs)
        OBVIOUS
      <3>1. IsPrefix(<<"ACKofFIN">>, network[local])
        BY <2>8 DEF LastAck
      <3>2. Tail(network[local]) \in Seq(Msgs)
        BY <3>0, <3>1, PrefixOneNonEmpty
      <3>. QED  BY <2>8, <3>2 DEF LastAck
    <2>9. CASE TimeWait(local, remote)
      BY <2>9 DEF TimeWait
    <2>10. CASE Note2(local, remote)
      <3>0. network[local] \in Seq(Msgs) /\ network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>1. IsPrefix(<<"FIN", "ACKofFIN">>, network[local])
        BY <2>10 DEF Note2
      <3>2. Len(network[local]) >= 2
        BY <3>0, <3>1, PrefixTwoNonEmpty
      <3>3. SubSeq(network[local], 3, Len(network[local])) \in Seq(Msgs)
        BY <3>0, <3>2, SubSeqProperties
      <3>4. Append(network[remote], "ACKofFIN") \in Seq(Msgs)
        BY <3>0
      <3>. QED  BY <2>10, <3>3, <3>4 DEF Note2
    <2>. QED  BY <1>sys, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8,
                <2>9, <2>10
  <1>system. CASE System
    <2>. PICK local \in Peers, remote \in Peers :
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
      BY <1>system DEF System
    <2>. QED  BY <1>sys
  <1>reset. CASE Reset
    <2>. PICK local \in Peers, remote \in Peers : Note3(local, remote)
      BY <1>reset DEF Reset
    <2>. USE DEF Note3
    <2>1. CASE /\ tcb[local]
                /\ network' = [network EXCEPT ![remote] = Append(@, "RST")]
                /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]
      <3>. network[remote] \in Seq(Msgs)
        OBVIOUS
      <3>. Append(network[remote], "RST") \in Seq(Msgs)
        OBVIOUS
      <3>. QED  BY <2>1
    <2>2. CASE /\ IsPrefix(<<"RST">>, network[local])
                /\ network' = [network EXCEPT ![local] = Tail(network[local])]
                /\ \/ connstate' = [connstate EXCEPT ![local] = "LISTEN"]
                   \/ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
      <3>0. network[local] \in Seq(Msgs)
        OBVIOUS
      <3>1. Tail(network[local]) \in Seq(Msgs)
        BY <3>0, <2>2, PrefixOneNonEmpty
      <3>. QED  BY <2>2, <3>1
    <2>. QED  BY <2>1, <2>2
  <1>stutter. CASE UNCHANGED vars
    BY <1>stutter DEF vars
  <1>. QED  BY <1>user, <1>system, <1>reset, <1>stutter DEF Next

THEOREM TypeCorrect == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY DEF Init, TypeOK, States
  <1>. QED  BY <1>1, TypeOKInductive, PTL DEF Spec

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
(* Inductive strengthening for the proof of Spec => []Inv.                 *)
(*                                                                         *)
(* The seven Aux clauses below were discovered using Apalache's           *)
(* inductive-invariant search (see specifications/tcp/IndInv_apa.tla,     *)
(* the cfg files IndInv_apa.cfg and IndInv_apa_init.cfg, and the         *)
(* commit message of the corresponding commit for the iteration log).    *)
(***************************************************************************)
HasMsg(m, p) ==
  \E i \in 1..Len(network[p]) : network[p][i] = m

LastMsg(p) == network[p][Len(network[p])]

PostEstStrict == {"ESTABLISHED", "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING",
                  "CLOSE-WAIT", "LAST-ACK", "TIME-WAIT"}
PostEst       == PostEstStrict \cup {"CLOSED"}

Aux_singleton_RST ==
  \A p, q \in Peers :
    (p # q /\ network[p] = <<"RST">> /\ network[q] = <<>>)
       => connstate[q] # "ESTABLISHED"

Aux_singleton_ACK ==
  \A p, q \in Peers :
    (p # q /\ network[p] = <<"ACK">> /\ network[q] = <<>>
            /\ connstate[p] = "SYN-RECEIVED")
       => connstate[q] = "ESTABLISHED"

Aux_singleton_ACKofFIN ==
  \A p, q \in Peers :
    (p # q /\ network[p] = <<"ACKofFIN">> /\ network[q] = <<>>
            /\ connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"})
       => connstate[q] # "ESTABLISHED"

Aux_EST_evidence ==
  \A p, q \in Peers :
    (p # q /\ connstate[p] = "ESTABLISHED")
       => \/ connstate[q] \in PostEst
          \/ HasMsg("SYN", p)        \/ HasMsg("SYN", q)
          \/ HasMsg("ACK", q)        \/ HasMsg("ACK", p)
          \/ HasMsg("SYN,ACK", q)    \/ HasMsg("SYN,ACK", p)
          \/ HasMsg("FIN", p)        \/ HasMsg("FIN", q)
          \/ HasMsg("ACKofFIN", p)   \/ HasMsg("ACKofFIN", q)
          \/ HasMsg("RST", p)        \/ HasMsg("RST", q)

Aux_LastMsg ==
  \A p, q \in Peers :
    (p # q /\ network[p] # <<>>) =>
      /\ connstate[q] = "SYN-RECEIVED"  => LastMsg(p) = "SYN,ACK"
      /\ connstate[q] = "FIN-WAIT-1"    => LastMsg(p) \in {"FIN", "RST"}
      /\ connstate[q] = "CLOSE-WAIT"    => LastMsg(p) = "ACKofFIN"
      /\ connstate[q] = "LAST-ACK"      => LastMsg(p) = "FIN"
      /\ connstate[q] = "CLOSING"       => LastMsg(p) = "ACKofFIN"
      /\ connstate[q] = "SYN-SENT"      => LastMsg(p) = "SYN"

Aux_RST_at_end ==
  \A p, q \in Peers :
    (p # q /\ network[p] # <<>> /\ LastMsg(p) = "RST")
       => connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}

IndInv ==
  /\ TypeOK
  /\ Inv
  /\ Aux_singleton_RST
  /\ Aux_singleton_ACK
  /\ Aux_singleton_ACKofFIN
  /\ Aux_EST_evidence
  /\ Aux_LastMsg
  /\ Aux_RST_at_end

(***************************************************************************)
(* Initial state.                                                          *)
(***************************************************************************)
THEOREM IndInvInit == Init => IndInv
  <1>. SUFFICES ASSUME Init  PROVE IndInv
    OBVIOUS
  <1>. USE DEF Init
  <1>1. \A p \in Peers : connstate[p] = "CLOSED" /\ network[p] = <<>> /\ tcb[p] = FALSE
    OBVIOUS
  <1>2. TypeOK
    BY <1>1 DEF TypeOK, States
  <1>3. Inv
    BY <1>1 DEF Inv
  <1>4. Aux_singleton_RST  /\  Aux_singleton_ACK  /\  Aux_singleton_ACKofFIN
    BY <1>1 DEF Aux_singleton_RST, Aux_singleton_ACK, Aux_singleton_ACKofFIN
  <1>5. Aux_EST_evidence
    BY <1>1 DEF Aux_EST_evidence
  <1>6. Aux_LastMsg
    BY <1>1 DEF Aux_LastMsg
  <1>7. Aux_RST_at_end
    BY <1>1 DEF Aux_RST_at_end
  <1>. QED  BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF IndInv

(***************************************************************************)
(* Inductive step for IndInv.                                              *)
(*                                                                         *)
(* The proof has two parts: a stutter case (trivial) and a per-action     *)
(* analysis covering every TCP transition.                                 *)
(***************************************************************************)

\* The "stutter" case is trivial: vars unchanged ⇒ every clause is the
\* same primed and unprimed.
LEMMA IndInvStutter == IndInv /\ UNCHANGED vars => IndInv'
  <1>. SUFFICES ASSUME IndInv, UNCHANGED vars PROVE IndInv'
    OBVIOUS
  <1>. USE DEF vars
  <1>1. tcb' = tcb /\ connstate' = connstate /\ network' = network
    OBVIOUS
  <1>. QED
    BY <1>1
       DEF IndInv, TypeOK, Inv,
           Aux_singleton_RST, Aux_singleton_ACK, Aux_singleton_ACKofFIN,
           Aux_EST_evidence, Aux_LastMsg, Aux_RST_at_end,
           HasMsg, LastMsg

(***************************************************************************)
(* The non-stutter case is split into the three top-level disjuncts of    *)
(* Next.  Each sub-lemma takes IndInv, the action, and TypeOK' (already   *)
(* discharged via TypeOKInductive) and proves the remaining clauses.    *)
(***************************************************************************)

\* User actions: PASSIVE_OPEN, CLOSE_SYN_SENT, CLOSE_LISTEN do NOT change
\* network[_].  ACTIVE_OPEN, SEND append "SYN" to n[remote].
\* CLOSE_SYN_RECEIVED, CLOSE_ESTABLISHED, CLOSE_CLOSE_WAIT append "FIN".
\* In every case connstate[local] changes; connstate[r] for r # local is
\* unchanged.  None of these actions transition local INTO ESTABLISHED.

LEMMA IndInvUser ==
  ASSUME IndInv, TypeOK',
         NEW local \in Peers, NEW remote \in Peers,
         \/ PASSIVE_OPEN(local, remote)
         \/ ACTIVE_OPEN(local, remote)
         \/ CLOSE_SYN_SENT(local, remote)
         \/ CLOSE_SYN_RECEIVED(local, remote)
         \/ CLOSE_LISTEN(local, remote)
         \/ CLOSE_ESTABLISHED(local, remote)
         \/ CLOSE_CLOSE_WAIT(local, remote)
         \/ SEND(local, remote)
  PROVE  IndInv'
  <1>. USE PeersAB DEF IndInv
  <1>1. CASE PASSIVE_OPEN(local, remote)
    <2>. USE <1>1 DEF PASSIVE_OPEN
    <2>. /\ network' = network
         /\ connstate' = [connstate EXCEPT ![local] = "LISTEN"]
         /\ connstate'[local] = "LISTEN"
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : network'[r] = network[r]
      BY DEF TypeOK
    <2>1. Inv'
      BY DEF Inv
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q,
                            network'[p] = <<"RST">>,
                            network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. network[p] = <<"RST">> /\ network[q] = <<>>
        OBVIOUS
      <3>2. connstate[q] # "ESTABLISHED"
        BY <3>1 DEF Aux_singleton_RST
      <3>. QED
        BY <3>2
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q,
                            network'[p] = <<"ACK">>,
                            network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. network[p] = <<"ACK">> /\ network[q] = <<>>
        OBVIOUS
      <3>2. connstate[p] = "SYN-RECEIVED"
        \* p # local since action makes local LISTEN, not SR.
        BY DEF TypeOK
      <3>3. connstate[q] = "ESTABLISHED"
        BY <3>1, <3>2 DEF Aux_singleton_ACK
      <3>4. q # local
        \* PASSIVE_OPEN required local=CLOSED, but q=EST.
        BY <3>3 DEF TypeOK
      <3>. QED
        BY <3>3, <3>4
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q,
                            network'[p] = <<"ACKofFIN">>,
                            network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. network[p] = <<"ACKofFIN">> /\ network[q] = <<>>
        OBVIOUS
      <3>2. connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
        BY DEF TypeOK
      <3>. QED
        BY <3>1, <3>2 DEF Aux_singleton_ACKofFIN
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q,
                            connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)'        \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)'        \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)'    \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)'        \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)'   \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)'        \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>3. \A m \in Msgs, r \in Peers : HasMsg(m, r) <=> HasMsg(m, r)'
        BY DEF HasMsg
      <3>5. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>5 DEF TypeOK
        <4>2. \/ connstate[q] \in PostEst
              \/ HasMsg("SYN", p) \/ HasMsg("SYN", q)
              \/ HasMsg("ACK", q) \/ HasMsg("ACK", p)
              \/ HasMsg("SYN,ACK", q) \/ HasMsg("SYN,ACK", p)
              \/ HasMsg("FIN", p) \/ HasMsg("FIN", q)
              \/ HasMsg("ACKofFIN", p) \/ HasMsg("ACKofFIN", q)
              \/ HasMsg("RST", p) \/ HasMsg("RST", q)
          BY <3>1 DEF Aux_EST_evidence
        <4>. QED
          BY <3>3, <4>1, <4>2 DEF PostEst, PostEstStrict
      <3>6. CASE q = local
        \* connstate[local] was CLOSED; CLOSED in PostEst.  After PASSIVE_OPEN
        \* connstate[local] = LISTEN, NOT in PostEst.  We instead derive a
        \* HasMsg disjunct from Inv: with p=EST and q=CLOSED, Inv forces at
        \* least one network to be non-empty (otherwise EST agreement fails).
        \* Any element of a non-empty network is in Msgs (TypeOK), giving the
        \* corresponding HasMsg disjunct.
        <4>1. connstate[q] = "CLOSED"
          BY <3>6
        <4>2. ~ (network[p] = <<>> /\ network[q] = <<>>)
          <5>1. {r \in Peers : network[r] = <<>>} \subseteq Peers
            OBVIOUS
          <5>2. p \in Peers /\ q \in Peers /\ p # q
            OBVIOUS
          <5>. SUFFICES ASSUME network[p] = <<>>, network[q] = <<>>
                        PROVE  FALSE
            OBVIOUS
          <5>3. p \in {r \in Peers : network[r] = <<>>}
                /\ q \in {r \in Peers : network[r] = <<>>}
            OBVIOUS
          <5>4. connstate[p] = "ESTABLISHED" <=> connstate[q] = "ESTABLISHED"
            BY <5>3 DEF Inv
          <5>. QED
            BY <3>1, <4>1, <5>4
        <4>3. network[p] # <<>> \/ network[q] # <<>>
          BY <4>2
        <4>4. network[p] \in Seq(Msgs) /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>5. \/ HasMsg("SYN", p) \/ HasMsg("SYN", q)
              \/ HasMsg("ACK", q) \/ HasMsg("ACK", p)
              \/ HasMsg("SYN,ACK", q) \/ HasMsg("SYN,ACK", p)
              \/ HasMsg("FIN", p) \/ HasMsg("FIN", q)
              \/ HasMsg("ACKofFIN", p) \/ HasMsg("ACKofFIN", q)
              \/ HasMsg("RST", p) \/ HasMsg("RST", q)
          <5>1. CASE network[p] # <<>>
            <6>1. Len(network[p]) >= 1 /\ network[p][1] \in Msgs
              BY <4>4, <5>1
            <6>2. \E i \in 1..Len(network[p]) : network[p][i] = network[p][1]
              BY <6>1
            <6>. QED
              BY <6>1, <6>2 DEF HasMsg, Msgs
          <5>2. CASE network[q] # <<>>
            <6>1. Len(network[q]) >= 1 /\ network[q][1] \in Msgs
              BY <4>4, <5>2
            <6>2. \E i \in 1..Len(network[q]) : network[q][i] = network[q][1]
              BY <6>1
            <6>. QED
              BY <6>1, <6>2 DEF HasMsg, Msgs
          <5>. QED
            BY <4>3, <5>1, <5>2
        <4>. QED
          BY <3>3, <4>5 DEF Msgs
      <3>. QED
        BY <3>5, <3>6
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. network[p] # <<>> /\ network[p] = network'[p] /\ LastMsg(p)' = LastMsg(p)
        BY DEF LastMsg
      <3>2. q # local =>
              /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p) = "SYN,ACK"
              /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p) \in {"FIN", "RST"}
              /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p) = "ACKofFIN"
              /\ connstate'[q] = "LAST-ACK"      => LastMsg(p) = "FIN"
              /\ connstate'[q] = "CLOSING"       => LastMsg(p) = "ACKofFIN"
              /\ connstate'[q] = "SYN-SENT"      => LastMsg(p) = "SYN"
        BY <3>1 DEF Aux_LastMsg
      <3>3. q = local => connstate'[q] = "LISTEN"
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. network[p] # <<>> /\ LastMsg(p) = "RST"
        BY DEF LastMsg
      <3>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY <3>1 DEF Aux_RST_at_end
      <3>. QED  BY <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv
  (*************************************************************************)
  (* The next two user actions also leave network unchanged and merely    *)
  (* transition connstate[local] to CLOSED.  We re-use the same per-aux   *)
  (* structure as PASSIVE_OPEN above; the only differences are the pre-  *)
  (* state of local and the post-state value.                              *)
  (*************************************************************************)
  <1>2. CASE CLOSE_SYN_SENT(local, remote)
    <2>. USE <1>2 DEF CLOSE_SYN_SENT
    <2>. /\ network' = network
         /\ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
         /\ connstate'[local] = "CLOSED"
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : network'[r] = network[r]
         /\ connstate[local] = "SYN-SENT"
      BY DEF TypeOK
    <2>1. Inv'
      BY DEF Inv
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. network[p] = <<"RST">> /\ network[q] = <<>>
        OBVIOUS
      <3>2. connstate[q] # "ESTABLISHED"
        BY <3>1 DEF Aux_singleton_RST
      <3>. QED  BY <3>2 DEF TypeOK
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. connstate[p] = "SYN-RECEIVED"
        BY DEF TypeOK
      <3>2. connstate[q] = "ESTABLISHED"
        BY <3>1 DEF Aux_singleton_ACK
      <3>3. q # local
        BY <3>2 DEF TypeOK
      <3>. QED  BY <3>2, <3>3 DEF TypeOK
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
        BY DEF TypeOK
      <3>2. connstate[q] # "ESTABLISHED"
        BY <3>1 DEF Aux_singleton_ACKofFIN
      <3>. QED  BY <3>2 DEF TypeOK
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. \A m \in Msgs, r \in Peers : HasMsg(m, r) <=> HasMsg(m, r)'
        BY DEF HasMsg
      <3>3. CASE q = local
        BY <3>3 DEF PostEst, PostEstStrict
      <3>4. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>4 DEF TypeOK
        <4>. QED
          BY <3>1, <3>2, <4>1 DEF Aux_EST_evidence, Msgs, PostEst, PostEstStrict
      <3>. QED  BY <3>3, <3>4
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. network[p] # <<>> /\ LastMsg(p)' = LastMsg(p)
        BY DEF LastMsg
      <3>2. q # local => connstate'[q] = connstate[q]
        BY DEF TypeOK
      <3>3. q = local => connstate'[q] = "CLOSED"
        OBVIOUS
      <3>. QED
        BY <3>1, <3>2, <3>3 DEF Aux_LastMsg
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. network[p] # <<>> /\ LastMsg(p) = "RST"
        BY DEF LastMsg
      <3>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY <3>1 DEF Aux_RST_at_end
      <3>3. q # local => connstate'[q] = connstate[q]
        BY DEF TypeOK
      <3>4. q = local => connstate'[q] = "CLOSED"
        OBVIOUS
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  <1>3. CASE CLOSE_LISTEN(local, remote)
    <2>. USE <1>3 DEF CLOSE_LISTEN
    <2>. /\ network' = network
         /\ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
         /\ connstate'[local] = "CLOSED"
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : network'[r] = network[r]
         /\ connstate[local] = "LISTEN"
      BY DEF TypeOK
    <2>1. Inv'
      BY DEF Inv
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. network[p] = <<"RST">> /\ network[q] = <<>>
        OBVIOUS
      <3>2. connstate[q] # "ESTABLISHED"
        BY <3>1 DEF Aux_singleton_RST
      <3>. QED  BY <3>2 DEF TypeOK
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. connstate[p] = "SYN-RECEIVED"
        BY DEF TypeOK
      <3>2. connstate[q] = "ESTABLISHED"
        BY <3>1 DEF Aux_singleton_ACK
      <3>3. q # local
        BY <3>2 DEF TypeOK
      <3>. QED  BY <3>2, <3>3
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
        BY DEF TypeOK
      <3>. QED  BY <3>1 DEF Aux_singleton_ACKofFIN
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. \A m \in Msgs, r \in Peers : HasMsg(m, r) <=> HasMsg(m, r)'
        BY DEF HasMsg
      <3>3. CASE q = local
        BY <3>3 DEF PostEst, PostEstStrict
      <3>4. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>4 DEF TypeOK
        <4>. QED
          BY <3>1, <3>2, <4>1 DEF Aux_EST_evidence, Msgs, PostEst, PostEstStrict
      <3>. QED  BY <3>3, <3>4
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. network[p] # <<>> /\ LastMsg(p)' = LastMsg(p)
        BY DEF LastMsg
      <3>2. q # local => connstate'[q] = connstate[q]
        BY DEF TypeOK
      <3>3. q = local => connstate'[q] = "CLOSED"
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3 DEF Aux_LastMsg
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. network[p] # <<>> /\ LastMsg(p) = "RST"
        BY DEF LastMsg
      <3>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY <3>1 DEF Aux_RST_at_end
      <3>3. q # local => connstate'[q] = connstate[q]
        BY DEF TypeOK
      <3>4. q = local => connstate'[q] = "CLOSED"
        OBVIOUS
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  (*************************************************************************)
  (* The remaining five user actions all append one message to n[remote]  *)
  (* and transition local to a non-EST state.  We bundle them via a      *)
  (* helper sub-lemma parameterised on the appended message and the       *)
  (* target state.                                                         *)
  (*************************************************************************)
  <1>4. CASE ACTIVE_OPEN(local, remote)
    <2>. USE <1>4 DEF ACTIVE_OPEN
    <2>. /\ network' = [network EXCEPT ![remote] = Append(@, "SYN")]
         /\ connstate' = [connstate EXCEPT ![local] = "SYN-SENT"]
         /\ connstate'[local] = "SYN-SENT"
         /\ network'[remote] = Append(network[remote], "SYN")
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : r # remote => network'[r] = network[r]
         /\ connstate[local] = "CLOSED"
      BY DEF TypeOK
    <2>. local # remote
      OBVIOUS
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. \A p \in Peers : network'[remote] # <<>>
        BY DEF TypeOK, Msgs
      <3>. {p \in Peers : network'[p] = <<>>} \subseteq {p \in Peers : p # remote}
        OBVIOUS
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ l # remote /\ r # remote
           /\ network[l] = <<>> /\ network[r] = <<>>
        OBVIOUS
      <3>. l \in {p \in Peers : network[p] = <<>>}
           /\ r \in {p \in Peers : network[p] = <<>>}
        OBVIOUS
      <3>. connstate[l] = "ESTABLISHED" <=> connstate[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ (l # local => connstate'[l] = connstate[l])
           /\ (r # local => connstate'[r] = connstate[r])
           /\ (l = local => connstate'[l] = "SYN-SENT")
           /\ (r = local => connstate'[r] = "SYN-SENT")
        OBVIOUS
      <3>. QED
        OBVIOUS
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>2. p # remote
        \* If p = remote, network'[p] = Append(network[p], "SYN") which has
        \* "SYN" as the last element, not "RST" alone.
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>1. network'[p] = Append(network[p], "SYN")
          OBVIOUS
        <4>2. Append(network[p], "SYN") = <<"RST">>
          BY <4>1
        <4>3. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED
          BY <4>2, <4>3
      <3>3. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED
        BY <3>3
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>1. Append(network[p], "SYN") = <<"ACK">>
          OBVIOUS
        <4>2. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  BY <4>1, <4>2
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>3. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED
        BY <3>3
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>1. Append(network[p], "SYN") = <<"ACKofFIN">>
          OBVIOUS
        <4>2. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  BY <4>1, <4>2
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>3. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED
        BY <3>3
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      \* Either q = local (just opened), or q is the other peer.
      \* In the q = local case the new SYN sits in n'[remote] = n'[p];
      \* HasMsg("SYN", p)' holds because p = remote.
      \* In the q # local case, connstate'[q] = connstate[q] and the
      \* HasMsg disjuncts are unchanged.
      <3>2. CASE q = local
        <4>. p = remote
          BY <3>1, <3>2, PeersAB
        <4>1. network'[p] = Append(network[p], "SYN")
          OBVIOUS
        <4>2. network[p] \in Seq(Msgs) /\ Len(network[p]) \in Nat
          BY DEF TypeOK, Msgs
        <4>3. Len(network'[p]) = Len(network[p]) + 1
              /\ network'[p][Len(network'[p])] = "SYN"
          BY <4>1, <4>2
        <4>4. \E i \in 1..Len(network'[p]) : network'[p][i] = "SYN"
          BY <4>3
        <4>. QED
          BY <4>4 DEF HasMsg
      <3>3. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>3 DEF TypeOK
        <4>2. \/ connstate[q] \in PostEst
              \/ HasMsg("SYN", p) \/ HasMsg("SYN", q)
              \/ HasMsg("ACK", q) \/ HasMsg("ACK", p)
              \/ HasMsg("SYN,ACK", q) \/ HasMsg("SYN,ACK", p)
              \/ HasMsg("FIN", p) \/ HasMsg("FIN", q)
              \/ HasMsg("ACKofFIN", p) \/ HasMsg("ACKofFIN", q)
              \/ HasMsg("RST", p) \/ HasMsg("RST", q)
          BY <3>1 DEF Aux_EST_evidence
        <4>3. \A m \in Msgs, r \in Peers : HasMsg(m, r) => HasMsg(m, r)'
          \* Append-only: every pre witness is also a post witness (with the
          \* same index, since indices below Len(network[r]) are unaffected).
          <5>. SUFFICES ASSUME NEW m \in Msgs, NEW r \in Peers, HasMsg(m, r)
                       PROVE  HasMsg(m, r)'
            OBVIOUS
          <5>1. \E i \in 1..Len(network[r]) : network[r][i] = m
            BY DEF HasMsg
          <5>2. CASE r = remote
            <6>1. network[r] \in Seq(Msgs) /\ network[r] = network[remote]
              BY <5>2 DEF TypeOK, Msgs
            <6>2. network'[r] = Append(network[r], "SYN")
              BY <5>2
            <6>3. Len(network'[r]) = Len(network[r]) + 1
              BY <6>1, <6>2
            <6>4. \A i \in 1..Len(network[r]) : network'[r][i] = network[r][i]
              BY <6>1, <6>2
            <6>. QED
              BY <5>1, <6>3, <6>4 DEF HasMsg
          <5>3. CASE r # remote
            <6>1. network'[r] = network[r]
              BY <5>3
            <6>. QED
              BY <5>1, <6>1 DEF HasMsg
          <5>. QED  BY <5>2, <5>3
        <4>. QED
          BY <4>1, <4>2, <4>3 DEF Msgs, PostEst, PostEstStrict
      <3>. QED
        BY <3>2, <3>3
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE p = remote
        <4>. q # remote /\ q = local
          BY <3>1, PeersAB
        <4>1. connstate'[q] = "SYN-SENT"
          OBVIOUS
        <4>2. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>3. network'[p] = Append(network[p], "SYN")
          BY <3>1
        <4>4. LastMsg(p)' = "SYN"
          BY <4>2, <4>3 DEF LastMsg
        <4>. QED
          BY <4>1, <4>4
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p]
          BY <3>2
        <4>2. LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <4>1 DEF LastMsg
        <4>3. q # local
          \* If q = local then connstate'[q] = SYN-SENT, and Aux_LastMsg
          \* requires LastMsg(p) = SYN; but p # remote in this branch
          \* implies p = local, contradicting p # q.
          BY <3>2, PeersAB
        <4>4. connstate'[q] = connstate[q]
          BY <4>3 DEF TypeOK
        <4>. QED
          BY <4>2, <4>4 DEF Aux_LastMsg
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE p = remote
        \* LastMsg(p)' = "SYN" # "RST" -- vacuous.
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. network'[p] = Append(network[p], "SYN")  /\  LastMsg(p)' = "SYN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
          BY <4>1 DEF Aux_RST_at_end
        <4>3. q # local
          \* If q = local then connstate'[q] = SYN-SENT \notin
          \* {TW, CLOSED, LISTEN}; but pre connstate[q] = CLOSED is in
          \* the set so this is consistent only when q != local.  We
          \* take the easier route: p # remote implies p = local in
          \* the 2-peer model, so q # local follows from p # q.
          BY <3>2, PeersAB
        <4>4. connstate'[q] = connstate[q]
          BY <4>3 DEF TypeOK
        <4>. QED
          BY <4>2, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  (*************************************************************************)
  (* SEND mirrors ACTIVE_OPEN (LISTEN -> SS, append "SYN").                *)
  (*************************************************************************)
  <1>5. CASE SEND(local, remote)
    <2>. USE <1>5 DEF SEND
    <2>. /\ network' = [network EXCEPT ![remote] = Append(@, "SYN")]
         /\ connstate' = [connstate EXCEPT ![local] = "SYN-SENT"]
         /\ connstate'[local] = "SYN-SENT"
         /\ network'[remote] = Append(network[remote], "SYN")
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : r # remote => network'[r] = network[r]
         /\ connstate[local] = "LISTEN"
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ l # remote /\ r # remote
           /\ network[l] = <<>> /\ network[r] = <<>>
        BY DEF TypeOK, Msgs
      <3>. l \in {p \in Peers : network[p] = <<>>}
           /\ r \in {p \in Peers : network[p] = <<>>}
        OBVIOUS
      <3>. connstate[l] = "ESTABLISHED" <=> connstate[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. QED  OBVIOUS
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "SYN") = <<"RST">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "SYN") = <<"ACK">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "SYN") = <<"ACKofFIN">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. CASE q = local
        <4>. p = remote
          BY <3>1, <3>2, PeersAB
        <4>1. network[p] \in Seq(Msgs) /\ Len(network[p]) \in Nat
          BY DEF TypeOK, Msgs
        <4>2. network'[p] = Append(network[p], "SYN")
              /\ Len(network'[p]) = Len(network[p]) + 1
              /\ network'[p][Len(network'[p])] = "SYN"
          BY <4>1
        <4>. QED
          BY <4>2 DEF HasMsg
      <3>3. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>3 DEF TypeOK
        <4>2. \/ connstate[q] \in PostEst
              \/ HasMsg("SYN", p) \/ HasMsg("SYN", q)
              \/ HasMsg("ACK", q) \/ HasMsg("ACK", p)
              \/ HasMsg("SYN,ACK", q) \/ HasMsg("SYN,ACK", p)
              \/ HasMsg("FIN", p) \/ HasMsg("FIN", q)
              \/ HasMsg("ACKofFIN", p) \/ HasMsg("ACKofFIN", q)
              \/ HasMsg("RST", p) \/ HasMsg("RST", q)
          BY <3>1 DEF Aux_EST_evidence
        <4>3. \A m \in Msgs, r \in Peers : HasMsg(m, r) => HasMsg(m, r)'
          <5>. SUFFICES ASSUME NEW m \in Msgs, NEW r \in Peers, HasMsg(m, r)
                       PROVE  HasMsg(m, r)'
            OBVIOUS
          <5>1. \E i \in 1..Len(network[r]) : network[r][i] = m
            BY DEF HasMsg
          <5>2. CASE r = remote
            <6>1. network[r] \in Seq(Msgs)
              BY <5>2 DEF TypeOK, Msgs
            <6>2. network'[r] = Append(network[r], "SYN")
              BY <5>2
            <6>3. Len(network'[r]) = Len(network[r]) + 1
              BY <6>1, <6>2
            <6>4. \A i \in 1..Len(network[r]) : network'[r][i] = network[r][i]
              BY <6>1, <6>2
            <6>. QED
              BY <5>1, <6>3, <6>4 DEF HasMsg
          <5>3. CASE r # remote
            BY <5>1, <5>3 DEF HasMsg
          <5>. QED  BY <5>2, <5>3
        <4>. QED
          BY <4>1, <4>2, <4>3 DEF Msgs, PostEst, PostEstStrict
      <3>. QED  BY <3>2, <3>3
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE p = remote
        <4>. q # remote /\ q = local
          BY <3>1, PeersAB
        <4>. connstate'[q] = "SYN-SENT"
          OBVIOUS
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. network'[p] = Append(network[p], "SYN") /\ LastMsg(p)' = "SYN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. q # local
          BY <3>2, PeersAB
        <4>3. connstate'[q] = connstate[q]
          BY <4>2 DEF TypeOK
        <4>. QED
          BY <4>1, <4>3 DEF Aux_LastMsg
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE p = remote
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. LastMsg(p)' = "SYN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
          BY <4>1 DEF Aux_RST_at_end
        <4>3. q # local
          BY <3>2, PeersAB
        <4>4. connstate'[q] = connstate[q]
          BY <4>3 DEF TypeOK
        <4>. QED
          BY <4>2, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  (*************************************************************************)
  (* The three remaining CLOSE_* actions all append "FIN" to n[remote]    *)
  (* and transition local into a PostEst state (FW1 or LA).  Compared to *)
  (* ACTIVE_OPEN/SEND the Aux_EST_evidence case is easier because        *)
  (* connstate'[local] is already in PostEst.                             *)
  (*************************************************************************)
  <1>6. CASE CLOSE_SYN_RECEIVED(local, remote)
    <2>. USE <1>6 DEF CLOSE_SYN_RECEIVED
    <2>. /\ network' = [network EXCEPT ![remote] = Append(@, "FIN")]
         /\ connstate' = [connstate EXCEPT ![local] = "FIN-WAIT-1"]
         /\ connstate'[local] = "FIN-WAIT-1"
         /\ network'[remote] = Append(network[remote], "FIN")
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : r # remote => network'[r] = network[r]
         /\ connstate[local] = "SYN-RECEIVED"
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ l # remote /\ r # remote
           /\ network[l] = <<>> /\ network[r] = <<>>
        BY DEF TypeOK, Msgs
      <3>. l \in {p \in Peers : network[p] = <<>>}
           /\ r \in {p \in Peers : network[p] = <<>>}
        OBVIOUS
      <3>. connstate[l] = "ESTABLISHED" <=> connstate[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ (l = local => connstate'[l] = "FIN-WAIT-1")
           /\ (r = local => connstate'[r] = "FIN-WAIT-1")
        OBVIOUS
      <3>. QED  OBVIOUS
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "FIN") = <<"RST">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "FIN") = <<"ACK">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "FIN") = <<"ACKofFIN">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. CASE q = local
        \* connstate'[q] = "FIN-WAIT-1" \in PostEstStrict \subseteq PostEst.
        BY <3>2 DEF PostEst, PostEstStrict
      <3>3. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>3 DEF TypeOK
        <4>2. \/ connstate[q] \in PostEst
              \/ HasMsg("SYN", p) \/ HasMsg("SYN", q)
              \/ HasMsg("ACK", q) \/ HasMsg("ACK", p)
              \/ HasMsg("SYN,ACK", q) \/ HasMsg("SYN,ACK", p)
              \/ HasMsg("FIN", p) \/ HasMsg("FIN", q)
              \/ HasMsg("ACKofFIN", p) \/ HasMsg("ACKofFIN", q)
              \/ HasMsg("RST", p) \/ HasMsg("RST", q)
          BY <3>1 DEF Aux_EST_evidence
        <4>3. \A m \in Msgs, r \in Peers : HasMsg(m, r) => HasMsg(m, r)'
          <5>. SUFFICES ASSUME NEW m \in Msgs, NEW r \in Peers, HasMsg(m, r)
                       PROVE  HasMsg(m, r)'
            OBVIOUS
          <5>1. \E i \in 1..Len(network[r]) : network[r][i] = m
            BY DEF HasMsg
          <5>2. CASE r = remote
            <6>1. network[r] \in Seq(Msgs)
              BY <5>2 DEF TypeOK, Msgs
            <6>2. network'[r] = Append(network[r], "FIN")
              BY <5>2
            <6>3. Len(network'[r]) = Len(network[r]) + 1
              BY <6>1, <6>2
            <6>4. \A i \in 1..Len(network[r]) : network'[r][i] = network[r][i]
              BY <6>1, <6>2
            <6>. QED
              BY <5>1, <6>3, <6>4 DEF HasMsg
          <5>3. CASE r # remote
            BY <5>1, <5>3 DEF HasMsg
          <5>. QED  BY <5>2, <5>3
        <4>. QED
          BY <4>1, <4>2, <4>3 DEF Msgs, PostEst, PostEstStrict
      <3>. QED  BY <3>2, <3>3
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE p = remote
        <4>. q # remote /\ q = local
          BY <3>1, PeersAB
        <4>. connstate'[q] = "FIN-WAIT-1"
          OBVIOUS
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. network'[p] = Append(network[p], "FIN") /\ LastMsg(p)' = "FIN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. q # local
          BY <3>2, PeersAB
        <4>3. connstate'[q] = connstate[q]
          BY <4>2 DEF TypeOK
        <4>. QED
          BY <4>1, <4>3 DEF Aux_LastMsg
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE p = remote
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. LastMsg(p)' = "FIN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
          BY <4>1 DEF Aux_RST_at_end
        <4>3. q # local
          BY <3>2, PeersAB
        <4>4. connstate'[q] = connstate[q]
          BY <4>3 DEF TypeOK
        <4>. QED  BY <4>2, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  <1>7. CASE CLOSE_ESTABLISHED(local, remote)
    <2>. USE <1>7 DEF CLOSE_ESTABLISHED
    <2>. /\ network' = [network EXCEPT ![remote] = Append(@, "FIN")]
         /\ connstate' = [connstate EXCEPT ![local] = "FIN-WAIT-1"]
         /\ connstate'[local] = "FIN-WAIT-1"
         /\ network'[remote] = Append(network[remote], "FIN")
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : r # remote => network'[r] = network[r]
         /\ connstate[local] = "ESTABLISHED"
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ l # remote /\ r # remote /\ network[l] = <<>> /\ network[r] = <<>>
        BY DEF TypeOK, Msgs
      <3>. l \in {p \in Peers : network[p] = <<>>}
           /\ r \in {p \in Peers : network[p] = <<>>}
        OBVIOUS
      <3>. connstate[l] = "ESTABLISHED" <=> connstate[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ (l = local => connstate'[l] = "FIN-WAIT-1")
           /\ (r = local => connstate'[r] = "FIN-WAIT-1")
        OBVIOUS
      <3>. QED  OBVIOUS
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "FIN") = <<"RST">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "FIN") = <<"ACK">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "FIN") = <<"ACKofFIN">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. CASE q = local
        BY <3>2 DEF PostEst, PostEstStrict
      <3>3. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>3 DEF TypeOK
        <4>2. \/ connstate[q] \in PostEst
              \/ HasMsg("SYN", p) \/ HasMsg("SYN", q)
              \/ HasMsg("ACK", q) \/ HasMsg("ACK", p)
              \/ HasMsg("SYN,ACK", q) \/ HasMsg("SYN,ACK", p)
              \/ HasMsg("FIN", p) \/ HasMsg("FIN", q)
              \/ HasMsg("ACKofFIN", p) \/ HasMsg("ACKofFIN", q)
              \/ HasMsg("RST", p) \/ HasMsg("RST", q)
          BY <3>1 DEF Aux_EST_evidence
        <4>3. \A m \in Msgs, r \in Peers : HasMsg(m, r) => HasMsg(m, r)'
          <5>. SUFFICES ASSUME NEW m \in Msgs, NEW r \in Peers, HasMsg(m, r)
                       PROVE  HasMsg(m, r)'
            OBVIOUS
          <5>1. \E i \in 1..Len(network[r]) : network[r][i] = m
            BY DEF HasMsg
          <5>2. CASE r = remote
            <6>1. network[r] \in Seq(Msgs)
              BY <5>2 DEF TypeOK, Msgs
            <6>2. network'[r] = Append(network[r], "FIN")
              BY <5>2
            <6>3. Len(network'[r]) = Len(network[r]) + 1
              BY <6>1, <6>2
            <6>4. \A i \in 1..Len(network[r]) : network'[r][i] = network[r][i]
              BY <6>1, <6>2
            <6>. QED
              BY <5>1, <6>3, <6>4 DEF HasMsg
          <5>3. CASE r # remote
            BY <5>1, <5>3 DEF HasMsg
          <5>. QED  BY <5>2, <5>3
        <4>. QED
          BY <4>1, <4>2, <4>3 DEF Msgs, PostEst, PostEstStrict
      <3>. QED  BY <3>2, <3>3
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE p = remote
        <4>. q # remote /\ q = local
          BY <3>1, PeersAB
        <4>. connstate'[q] = "FIN-WAIT-1"
          OBVIOUS
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. network'[p] = Append(network[p], "FIN") /\ LastMsg(p)' = "FIN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. q # local
          BY <3>2, PeersAB
        <4>3. connstate'[q] = connstate[q]
          BY <4>2 DEF TypeOK
        <4>. QED
          BY <4>1, <4>3 DEF Aux_LastMsg
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE p = remote
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. LastMsg(p)' = "FIN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
          BY <4>1 DEF Aux_RST_at_end
        <4>3. q # local
          BY <3>2, PeersAB
        <4>4. connstate'[q] = connstate[q]
          BY <4>3 DEF TypeOK
        <4>. QED  BY <4>2, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  <1>8. CASE CLOSE_CLOSE_WAIT(local, remote)
    <2>. USE <1>8 DEF CLOSE_CLOSE_WAIT
    <2>. /\ network' = [network EXCEPT ![remote] = Append(@, "FIN")]
         /\ connstate' = [connstate EXCEPT ![local] = "LAST-ACK"]
         /\ connstate'[local] = "LAST-ACK"
         /\ network'[remote] = Append(network[remote], "FIN")
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : r # remote => network'[r] = network[r]
         /\ connstate[local] = "CLOSE-WAIT"
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ l # remote /\ r # remote /\ network[l] = <<>> /\ network[r] = <<>>
        BY DEF TypeOK, Msgs
      <3>. l \in {p \in Peers : network[p] = <<>>}
           /\ r \in {p \in Peers : network[p] = <<>>}
        OBVIOUS
      <3>. connstate[l] = "ESTABLISHED" <=> connstate[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ (l = local => connstate'[l] = "LAST-ACK")
           /\ (r = local => connstate'[r] = "LAST-ACK")
        OBVIOUS
      <3>. QED  OBVIOUS
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "FIN") = <<"RST">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "FIN") = <<"ACK">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "FIN") = <<"ACKofFIN">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  OBVIOUS
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. CASE q = local
        BY <3>2 DEF PostEst, PostEstStrict
      <3>3. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>3 DEF TypeOK
        <4>2. \/ connstate[q] \in PostEst
              \/ HasMsg("SYN", p) \/ HasMsg("SYN", q)
              \/ HasMsg("ACK", q) \/ HasMsg("ACK", p)
              \/ HasMsg("SYN,ACK", q) \/ HasMsg("SYN,ACK", p)
              \/ HasMsg("FIN", p) \/ HasMsg("FIN", q)
              \/ HasMsg("ACKofFIN", p) \/ HasMsg("ACKofFIN", q)
              \/ HasMsg("RST", p) \/ HasMsg("RST", q)
          BY <3>1 DEF Aux_EST_evidence
        <4>3. \A m \in Msgs, r \in Peers : HasMsg(m, r) => HasMsg(m, r)'
          <5>. SUFFICES ASSUME NEW m \in Msgs, NEW r \in Peers, HasMsg(m, r)
                       PROVE  HasMsg(m, r)'
            OBVIOUS
          <5>1. \E i \in 1..Len(network[r]) : network[r][i] = m
            BY DEF HasMsg
          <5>2. CASE r = remote
            <6>1. network[r] \in Seq(Msgs)
              BY <5>2 DEF TypeOK, Msgs
            <6>2. network'[r] = Append(network[r], "FIN")
              BY <5>2
            <6>3. Len(network'[r]) = Len(network[r]) + 1
              BY <6>1, <6>2
            <6>4. \A i \in 1..Len(network[r]) : network'[r][i] = network[r][i]
              BY <6>1, <6>2
            <6>. QED
              BY <5>1, <6>3, <6>4 DEF HasMsg
          <5>3. CASE r # remote
            BY <5>1, <5>3 DEF HasMsg
          <5>. QED  BY <5>2, <5>3
        <4>. QED
          BY <4>1, <4>2, <4>3 DEF Msgs, PostEst, PostEstStrict
      <3>. QED  BY <3>2, <3>3
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE p = remote
        <4>. q # remote /\ q = local
          BY <3>1, PeersAB
        <4>. connstate'[q] = "LAST-ACK"
          OBVIOUS
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. network'[p] = Append(network[p], "FIN") /\ LastMsg(p)' = "FIN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. q # local
          BY <3>2, PeersAB
        <4>3. connstate'[q] = connstate[q]
          BY <4>2 DEF TypeOK
        <4>. QED
          BY <4>1, <4>3 DEF Aux_LastMsg
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE p = remote
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. LastMsg(p)' = "FIN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
          BY <4>1 DEF Aux_RST_at_end
        <4>3. q # local
          BY <3>2, PeersAB
        <4>4. connstate'[q] = connstate[q]
          BY <4>3 DEF TypeOK
        <4>. QED  BY <4>2, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  <1>. QED  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8

(***************************************************************************)
(* System actions: 10 in total.  Each consumes from n[local] and may also *)
(* append to n[remote].  We start with TimeWait (no network change) and  *)
(* extend incrementally.                                                  *)
(***************************************************************************)
LEMMA IndInvSystem ==
  ASSUME IndInv, TypeOK',
         NEW local \in Peers, NEW remote \in Peers,
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
  PROVE  IndInv'
  <1>. USE PeersAB DEF IndInv
  <1>9. CASE TimeWait(local, remote)
    <2>. USE <1>9 DEF TimeWait
    <2>. /\ network' = network
         /\ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
         /\ connstate'[local] = "CLOSED"
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : network'[r] = network[r]
         /\ connstate[local] = "TIME-WAIT"
      BY DEF TypeOK
    <2>1. Inv'
      BY DEF Inv
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. network[p] = <<"RST">> /\ network[q] = <<>>
        OBVIOUS
      <3>2. connstate[q] # "ESTABLISHED"
        BY <3>1 DEF Aux_singleton_RST
      <3>. QED  BY <3>2 DEF TypeOK
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. connstate[p] = "SYN-RECEIVED"
        BY DEF TypeOK
      <3>2. connstate[q] = "ESTABLISHED"
        BY <3>1 DEF Aux_singleton_ACK
      <3>3. q # local
        BY <3>2 DEF TypeOK
      <3>. QED  BY <3>2, <3>3 DEF TypeOK
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
        BY DEF TypeOK
      <3>2. connstate[q] # "ESTABLISHED"
        BY <3>1 DEF Aux_singleton_ACKofFIN
      <3>. QED  BY <3>2 DEF TypeOK
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. \A m \in Msgs, r \in Peers : HasMsg(m, r) <=> HasMsg(m, r)'
        BY DEF HasMsg
      <3>3. CASE q = local
        \* connstate'[q] = CLOSED in PostEst.
        BY <3>3 DEF PostEst, PostEstStrict
      <3>4. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>4 DEF TypeOK
        <4>. QED
          BY <3>1, <3>2, <4>1 DEF Aux_EST_evidence, Msgs, PostEst, PostEstStrict
      <3>. QED  BY <3>3, <3>4
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. network[p] # <<>> /\ LastMsg(p)' = LastMsg(p)
        BY DEF LastMsg
      <3>2. q # local => connstate'[q] = connstate[q]
        BY DEF TypeOK
      <3>3. q = local => connstate'[q] = "CLOSED"
        OBVIOUS
      <3>. QED  BY <3>1, <3>2, <3>3 DEF Aux_LastMsg
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. network[p] # <<>> /\ LastMsg(p) = "RST"
        BY DEF LastMsg
      <3>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY <3>1 DEF Aux_RST_at_end
      <3>3. q # local => connstate'[q] = connstate[q]
        BY DEF TypeOK
      <3>4. q = local => connstate'[q] = "CLOSED"
        OBVIOUS
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  (*************************************************************************)
  (* Closing and LastAck: consume "ACKofFIN" from n[local] (Tail), no    *)
  (* append.  For Tail with pre-Len >= 2, the LAST element of n[local]  *)
  (* is unchanged; for pre-Len = 1, n'[local] = <<>>.                    *)
  (*************************************************************************)
  <1>10. CASE Closing(local, remote)
    <2>. USE <1>10 DEF Closing
    <2>. /\ network' = [network EXCEPT ![local] = Tail(network[local])]
         /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]
         /\ connstate'[local] = "TIME-WAIT"
         /\ network'[local] = Tail(network[local])
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : r # local => network'[r] = network[r]
         /\ connstate[local] = "CLOSING"
         /\ IsPrefix(<<"ACKofFIN">>, network[local])
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>head. /\ network[local] # <<>>
             /\ Head(network[local]) = "ACKofFIN"
             /\ Tail(network[local]) \in Seq(Msgs)
      BY PrefixOneNonEmpty DEF TypeOK, Msgs
    <2>tail. /\ Len(network'[local]) = Len(network[local]) - 1
             /\ Len(network[local]) >= 1
             /\ \A i \in 1..Len(network'[local]) : network'[local][i] = network[local][i + 1]
      BY <2>head DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>0. /\ network'[l] = <<>> /\ network'[r] = <<>>
            /\ (l # local => network[l] = network'[l])
            /\ (r # local => network[r] = network'[r])
            /\ (l = local => network[l] = <<"ACKofFIN">>)
            /\ (r = local => network[r] = <<"ACKofFIN">>)
        <4>. \A x \in Peers : x # local => network'[x] = network[x]
          OBVIOUS
        <4>. \A x \in Peers : (x = local /\ Tail(network[x]) = <<>>) =>
                   network[x] = <<"ACKofFIN">>
          BY <2>head
        <4>. \A x \in Peers : x = local => network'[x] = Tail(network[x])
          OBVIOUS
        <4>. QED  OBVIOUS
      \* Either l, r # local (and then network[l] = network[r] = <<>>; use Inv pre),
      \* or one of them is local and connstate' = "TIME-WAIT" # "ESTABLISHED".
      <3>1. CASE l # local /\ r # local
        <4>. network[l] = <<>> /\ network[r] = <<>>
          BY <3>0, <3>1
        <4>. l \in {p \in Peers : network[p] = <<>>}
             /\ r \in {p \in Peers : network[p] = <<>>}
          OBVIOUS
        <4>. connstate[l] = "ESTABLISHED" <=> connstate[r] = "ESTABLISHED"
          BY DEF Inv
        <4>. connstate'[l] = connstate[l] /\ connstate'[r] = connstate[r]
          BY <3>1 DEF TypeOK
        <4>. QED  OBVIOUS
      <3>2. CASE l = local
        \* connstate'[l] = "TIME-WAIT", so we need connstate'[r] # "ESTABLISHED".
        <4>1. connstate'[l] = "TIME-WAIT" /\ "TIME-WAIT" # "ESTABLISHED"
          BY <3>2
        <4>2. CASE r = local
          BY <3>2, <4>2, <4>1
        <4>3. CASE r # local
          <5>1. network[r] = <<>>
            BY <3>0, <4>3
          <5>2. network[local] = <<"ACKofFIN">> /\ local \in Peers /\ r \in Peers /\ local # r
            BY <3>2, <3>0, <4>3
          <5>3. connstate[local] = "CLOSING"
            OBVIOUS
          <5>4. connstate[r] # "ESTABLISHED"
            BY <5>1, <5>2, <5>3 DEF Aux_singleton_ACKofFIN
          <5>5. connstate'[r] = connstate[r]
            BY <4>3 DEF TypeOK
          <5>. QED  BY <4>1, <5>4, <5>5
        <4>. QED  BY <4>2, <4>3
      <3>3. CASE r = local /\ l # local
        <4>1. connstate'[r] = "TIME-WAIT" /\ "TIME-WAIT" # "ESTABLISHED"
          BY <3>3
        <4>2. network[l] = <<>> /\ network[local] = <<"ACKofFIN">>
              /\ local \in Peers /\ l \in Peers /\ local # l
          BY <3>0, <3>3
        <4>3. connstate[local] = "CLOSING"
          OBVIOUS
        <4>4. connstate[l] # "ESTABLISHED"
          BY <4>2, <4>3 DEF Aux_singleton_ACKofFIN
        <4>5. connstate'[l] = connstate[l]
          BY <3>3 DEF TypeOK
        <4>. QED  BY <4>1, <4>4, <4>5
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      \* Two sub-cases on q (= local or # local).
      <3>1. CASE q = local
        \* connstate'[q] = TW # EST.  Done.
        BY <3>1
      <3>2. CASE q # local
        \* connstate'[q] = connstate[q].  Use Aux_singleton_RST or
        \* TypeOK reasoning.
        <4>1. connstate'[q] = connstate[q]
          BY <3>2 DEF TypeOK
        <4>2. network[q] = <<>>
          BY <3>2
        <4>3. CASE p = local
          \* network'[p] = Tail.  For = <<"RST">>: network[p] = <<X, "RST">>
          \* with X = "ACKofFIN" (the prefix forced by <2>head).  So
          \* pre n[p] = <<"ACKofFIN", "RST">>, last = "RST".  By
          \* Aux_RST_at_end pre, connstate[q] in {TW, CLOSED, LISTEN}.
          <5>1. network[p] = <<"ACKofFIN", "RST">>
            <6>. Tail(network[p]) = <<"RST">>
              BY <4>3
            <6>. Head(network[p]) = "ACKofFIN" /\ network[p] # <<>>
              BY <4>3, <2>head
            <6>. QED
              BY DEF TypeOK, Msgs
          <5>2. LastMsg(p) = "RST" /\ network[p] # <<>>
            BY <5>1 DEF LastMsg
          <5>3. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>2 DEF Aux_RST_at_end
          <5>. QED  BY <4>1, <5>3
        <4>4. CASE p # local
          \* network'[p] = network[p] = <<"RST">>.  Pre Aux_singleton_RST applies.
          <5>1. network[p] = <<"RST">>
            BY <4>4
          <5>. QED
            BY <4>1, <5>1, <4>2 DEF Aux_singleton_RST
        <4>. QED  BY <4>3, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. p # local
        \* connstate'[local] = TW # SR.
        BY DEF TypeOK
      <3>2. connstate[p] = "SYN-RECEIVED"
        BY <3>1 DEF TypeOK
      <3>3. CASE q = local
        \* But pre Aux_singleton_ACK with these args (n[p]=<<"ACK">>,
        \* n[q]=Tail's pre = <<"ACKofFIN">>): pre n[q] # <<>>, so pre aux
        \* doesn't apply.  We instead derive: since connstate'[q] = TW
        \* and aux requires = EST, we need TW = EST -- false.  So we
        \* show this case is unreachable.
        <4>1. network'[p] = network[p]
          BY <3>1
        <4>2. network[p] = <<"ACK">>
          BY <4>1
        <4>3. \* Now n[p] = <<"ACK">>, n[q] = <<"ACKofFIN">>, p connstate = SR,
              \* q connstate = CLOSING.  Aux_LastMsg requires LastMsg(p) = SYN,ACK
              \* when q = SR, but here q is CLOSING and p is SR.  So we use
              \* Aux_LastMsg with the roles swapped: q (=local, here CLOSING)
              \* requires LastMsg(p) = ACKofFIN.  But network[p] = <<"ACK">>,
              \* LastMsg(p) = "ACK" # "ACKofFIN".  Contradiction.
              connstate[q] = "CLOSING" /\ network[p] # <<>>
          BY <3>3, <4>2
        <4>4. LastMsg(p) = "ACK"
          BY <4>2 DEF LastMsg
        <4>. QED
          BY <4>3, <4>4 DEF Aux_LastMsg
      <3>4. CASE q # local
        <4>1. network'[q] = network[q] /\ network'[p] = network[p]
          BY <3>4, <3>1
        <4>2. connstate'[q] = connstate[q]
          BY <3>4 DEF TypeOK
        <4>3. network[p] = <<"ACK">> /\ network[q] = <<>>
          BY <4>1
        <4>4. connstate[q] = "ESTABLISHED"
          BY <3>2, <4>3 DEF Aux_singleton_ACK
        <4>. QED  BY <4>2, <4>4
      <3>. QED  BY <3>3, <3>4
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. p # local
        \* connstate'[local] = TW \notin {FW1, CLOSING, LA}.
        BY DEF TypeOK
      <3>2. connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
        BY <3>1 DEF TypeOK
      <3>3. CASE q = local
        \* connstate'[q] = TW # EST.
        BY <3>3
      <3>4. CASE q # local
        <4>1. network'[p] = network[p] /\ network'[q] = network[q]
          BY <3>1, <3>4
        <4>2. connstate'[q] = connstate[q]
          BY <3>4 DEF TypeOK
        <4>3. network[p] = <<"ACKofFIN">> /\ network[q] = <<>>
          BY <4>1
        <4>. QED  BY <3>2, <4>2, <4>3 DEF Aux_singleton_ACKofFIN
      <3>. QED  BY <3>3, <3>4
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. CASE q = local
        \* connstate'[q] = TW \in PostEst.
        BY <3>2 DEF PostEst, PostEstStrict
      <3>3. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>3 DEF TypeOK
        <4>2. \/ connstate[q] \in PostEst
              \/ HasMsg("SYN", p) \/ HasMsg("SYN", q)
              \/ HasMsg("ACK", q) \/ HasMsg("ACK", p)
              \/ HasMsg("SYN,ACK", q) \/ HasMsg("SYN,ACK", p)
              \/ HasMsg("FIN", p) \/ HasMsg("FIN", q)
              \/ HasMsg("ACKofFIN", p) \/ HasMsg("ACKofFIN", q)
              \/ HasMsg("RST", p) \/ HasMsg("RST", q)
          BY <3>1 DEF Aux_EST_evidence
        \* p # local AND q # local: with 2 peers this is impossible since
        \* p, q both in Peers \ {local} but Peers \ {local} has cardinality 1.
        <4>3. \/ p = local \/ q = local
          BY <3>1, <3>3, PeersAB
        <4>. QED
          BY <3>1, <3>3, <4>3
      <3>. QED  BY <3>2, <3>3
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE q = local
        \* connstate'[q] = TW, not covered.
        BY <3>1
      <3>2. CASE q # local
        <4>0. connstate'[q] = connstate[q]
          BY <3>2 DEF TypeOK
        <4>1. CASE p = local
          \* p = local: LastMsg(p)' = LastMsg of Tail.  When Len(n[p]) >= 2,
          \* same as pre LastMsg.  When Len = 1, n'[p] = <<>>, vacuous.
          <5>0. network'[p] # <<>> /\ network'[p] = Tail(network[p])
                /\ network[p] \in Seq(Msgs)
                /\ network'[p] \in Seq(Msgs)
            BY <4>1 DEF TypeOK, Msgs
          <5>2. Len(network'[p]) >= 1
            BY <5>0, EmptySeq
          <5>1. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
            BY <4>1, <2>tail
          <5>1a. Len(network[p]) >= 2
            BY <5>1, <5>2
          <5>3. network'[p][Len(network'[p])] = network[p][Len(network[p])]
            BY <4>1, <2>tail, <5>1, <5>1a
          <5>4. LastMsg(p)' = LastMsg(p)
            BY <5>3, <5>1, <5>2 DEF LastMsg
          <5>5. network[p] # <<>>
            BY <5>1a
          <5>. QED  BY <4>0, <5>4, <5>5 DEF Aux_LastMsg
        <4>2. CASE p # local
          <5>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
            BY <4>2 DEF LastMsg
          <5>. QED  BY <4>0, <5>1 DEF Aux_LastMsg
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE q = local
        BY <3>1
      <3>2. CASE q # local
        <4>0. connstate'[q] = connstate[q]
          BY <3>2 DEF TypeOK
        <4>1. CASE p = local
          <5>0. network'[p] # <<>> /\ network'[p] = Tail(network[p])
                /\ network[p] \in Seq(Msgs)
                /\ network'[p] \in Seq(Msgs)
            BY <4>1 DEF TypeOK, Msgs
          <5>2. Len(network'[p]) >= 1
            BY <5>0, EmptySeq
          <5>1. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
            BY <4>1, <2>tail
          <5>1a. Len(network[p]) >= 2
            BY <5>1, <5>2
          <5>3. network'[p][Len(network'[p])] = network[p][Len(network[p])]
            BY <4>1, <2>tail, <5>1, <5>1a
          <5>4. LastMsg(p)' = LastMsg(p) /\ LastMsg(p) = "RST" /\ network[p] # <<>>
            BY <5>3, <5>1, <5>2, <5>1a DEF LastMsg
          <5>5. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>4 DEF Aux_RST_at_end
          <5>. QED  BY <4>0, <5>5
        <4>2. CASE p # local
          <5>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
            BY <4>2 DEF LastMsg
          <5>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>1 DEF Aux_RST_at_end
          <5>. QED  BY <4>0, <5>2
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  (*************************************************************************)
  (* LastAck: same shape as Closing -- consume "ACKofFIN" via Tail, no    *)
  (* append.  Transitions LA -> CLOSED.                                    *)
  (*************************************************************************)
  <1>11. CASE LastAck(local, remote)
    <2>. USE <1>11 DEF LastAck
    <2>. /\ network' = [network EXCEPT ![local] = Tail(network[local])]
         /\ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
         /\ connstate'[local] = "CLOSED"
         /\ network'[local] = Tail(network[local])
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : r # local => network'[r] = network[r]
         /\ connstate[local] = "LAST-ACK"
         /\ IsPrefix(<<"ACKofFIN">>, network[local])
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>head. /\ network[local] # <<>>
             /\ Head(network[local]) = "ACKofFIN"
             /\ Tail(network[local]) \in Seq(Msgs)
      BY PrefixOneNonEmpty DEF TypeOK, Msgs
    <2>tail. /\ Len(network'[local]) = Len(network[local]) - 1
             /\ Len(network[local]) >= 1
             /\ \A i \in 1..Len(network'[local]) : network'[local][i] = network[local][i + 1]
      BY <2>head DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>0. /\ network'[l] = <<>> /\ network'[r] = <<>>
            /\ (l # local => network[l] = network'[l])
            /\ (r # local => network[r] = network'[r])
            /\ (l = local => network[l] = <<"ACKofFIN">>)
            /\ (r = local => network[r] = <<"ACKofFIN">>)
        <4>. \A x \in Peers : x # local => network'[x] = network[x]
          OBVIOUS
        <4>. \A x \in Peers : (x = local /\ Tail(network[x]) = <<>>) =>
                   network[x] = <<"ACKofFIN">>
          BY <2>head
        <4>. \A x \in Peers : x = local => network'[x] = Tail(network[x])
          OBVIOUS
        <4>. QED  OBVIOUS
      <3>1. CASE l # local /\ r # local
        <4>. network[l] = <<>> /\ network[r] = <<>>
          BY <3>0, <3>1
        <4>. l \in {p \in Peers : network[p] = <<>>}
             /\ r \in {p \in Peers : network[p] = <<>>}
          OBVIOUS
        <4>. connstate[l] = "ESTABLISHED" <=> connstate[r] = "ESTABLISHED"
          BY DEF Inv
        <4>. connstate'[l] = connstate[l] /\ connstate'[r] = connstate[r]
          BY <3>1 DEF TypeOK
        <4>. QED  OBVIOUS
      <3>2. CASE l = local
        <4>1. connstate'[l] = "CLOSED" /\ "CLOSED" # "ESTABLISHED"
          BY <3>2
        <4>2. CASE r = local
          BY <3>2, <4>2, <4>1
        <4>3. CASE r # local
          <5>1. network[r] = <<>>
            BY <3>0, <4>3
          <5>2. network[local] = <<"ACKofFIN">> /\ local \in Peers /\ r \in Peers /\ local # r
            BY <3>2, <3>0, <4>3
          <5>3. connstate[local] = "LAST-ACK"
            OBVIOUS
          <5>4. connstate[r] # "ESTABLISHED"
            BY <5>1, <5>2, <5>3 DEF Aux_singleton_ACKofFIN
          <5>5. connstate'[r] = connstate[r]
            BY <4>3 DEF TypeOK
          <5>. QED  BY <4>1, <5>4, <5>5
        <4>. QED  BY <4>2, <4>3
      <3>3. CASE r = local /\ l # local
        <4>1. connstate'[r] = "CLOSED" /\ "CLOSED" # "ESTABLISHED"
          BY <3>3
        <4>2. network[l] = <<>> /\ network[local] = <<"ACKofFIN">>
              /\ local \in Peers /\ l \in Peers /\ local # l
          BY <3>0, <3>3
        <4>3. connstate[local] = "LAST-ACK"
          OBVIOUS
        <4>4. connstate[l] # "ESTABLISHED"
          BY <4>2, <4>3 DEF Aux_singleton_ACKofFIN
        <4>5. connstate'[l] = connstate[l]
          BY <3>3 DEF TypeOK
        <4>. QED  BY <4>1, <4>4, <4>5
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. CASE q = local
        BY <3>1
      <3>2. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>2 DEF TypeOK
        <4>2. network[q] = <<>>
          BY <3>2
        <4>3. CASE p = local
          <5>1. network[p] = <<"ACKofFIN", "RST">>
            <6>. Tail(network[p]) = <<"RST">>
              BY <4>3
            <6>. Head(network[p]) = "ACKofFIN" /\ network[p] # <<>>
              BY <4>3, <2>head
            <6>. QED
              BY DEF TypeOK, Msgs
          <5>2. LastMsg(p) = "RST" /\ network[p] # <<>>
            BY <5>1 DEF LastMsg
          <5>3. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>2 DEF Aux_RST_at_end
          <5>. QED  BY <4>1, <5>3
        <4>4. CASE p # local
          <5>1. network[p] = <<"RST">>
            BY <4>4
          <5>. QED
            BY <4>1, <5>1, <4>2 DEF Aux_singleton_RST
        <4>. QED  BY <4>3, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. p # local
        BY DEF TypeOK
      <3>2. connstate[p] = "SYN-RECEIVED"
        BY <3>1 DEF TypeOK
      <3>3. CASE q = local
        <4>1. network'[p] = network[p]
          BY <3>1
        <4>2. network[p] = <<"ACK">>
          BY <4>1
        <4>3. connstate[q] = "LAST-ACK" /\ network[p] # <<>>
          BY <3>3, <4>2
        <4>4. LastMsg(p) = "ACK"
          BY <4>2 DEF LastMsg
        <4>. QED
          BY <4>3, <4>4 DEF Aux_LastMsg
      <3>4. CASE q # local
        <4>1. network'[q] = network[q] /\ network'[p] = network[p]
          BY <3>4, <3>1
        <4>2. connstate'[q] = connstate[q]
          BY <3>4 DEF TypeOK
        <4>3. network[p] = <<"ACK">> /\ network[q] = <<>>
          BY <4>1
        <4>4. connstate[q] = "ESTABLISHED"
          BY <3>2, <4>3 DEF Aux_singleton_ACK
        <4>. QED  BY <4>2, <4>4
      <3>. QED  BY <3>3, <3>4
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. p # local
        BY DEF TypeOK
      <3>2. connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
        BY <3>1 DEF TypeOK
      <3>3. CASE q = local
        BY <3>3
      <3>4. CASE q # local
        <4>1. network'[p] = network[p] /\ network'[q] = network[q]
          BY <3>1, <3>4
        <4>2. connstate'[q] = connstate[q]
          BY <3>4 DEF TypeOK
        <4>3. network[p] = <<"ACKofFIN">> /\ network[q] = <<>>
          BY <4>1
        <4>. QED  BY <3>2, <4>2, <4>3 DEF Aux_singleton_ACKofFIN
      <3>. QED  BY <3>3, <3>4
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. CASE q = local
        \* connstate'[q] = CLOSED \in PostEst.
        BY <3>2 DEF PostEst, PostEstStrict
      <3>3. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>3 DEF TypeOK
        <4>3. \/ p = local \/ q = local
          BY <3>1, <3>3, PeersAB
        <4>. QED
          BY <3>1, <3>3, <4>3
      <3>. QED  BY <3>2, <3>3
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE q = local
        BY <3>1
      <3>2. CASE q # local
        <4>0. connstate'[q] = connstate[q]
          BY <3>2 DEF TypeOK
        <4>1. CASE p = local
          <5>0. network'[p] # <<>> /\ network'[p] = Tail(network[p])
                /\ network[p] \in Seq(Msgs)
                /\ network'[p] \in Seq(Msgs)
            BY <4>1 DEF TypeOK, Msgs
          <5>2. Len(network'[p]) >= 1
            BY <5>0, EmptySeq
          <5>1. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
            BY <4>1, <2>tail
          <5>1a. Len(network[p]) >= 2
            BY <5>1, <5>2
          <5>3. network'[p][Len(network'[p])] = network[p][Len(network[p])]
            BY <4>1, <2>tail, <5>1, <5>1a
          <5>4. LastMsg(p)' = LastMsg(p)
            BY <5>3, <5>1, <5>2 DEF LastMsg
          <5>5. network[p] # <<>>
            BY <5>1a
          <5>. QED  BY <4>0, <5>4, <5>5 DEF Aux_LastMsg
        <4>2. CASE p # local
          <5>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
            BY <4>2 DEF LastMsg
          <5>. QED  BY <4>0, <5>1 DEF Aux_LastMsg
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE q = local
        BY <3>1
      <3>2. CASE q # local
        <4>0. connstate'[q] = connstate[q]
          BY <3>2 DEF TypeOK
        <4>1. CASE p = local
          <5>0. network'[p] # <<>> /\ network'[p] = Tail(network[p])
                /\ network[p] \in Seq(Msgs)
                /\ network'[p] \in Seq(Msgs)
            BY <4>1 DEF TypeOK, Msgs
          <5>2. Len(network'[p]) >= 1
            BY <5>0, EmptySeq
          <5>1. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
            BY <4>1, <2>tail
          <5>1a. Len(network[p]) >= 2
            BY <5>1, <5>2
          <5>3. network'[p][Len(network'[p])] = network[p][Len(network[p])]
            BY <4>1, <2>tail, <5>1, <5>1a
          <5>4. LastMsg(p)' = LastMsg(p) /\ LastMsg(p) = "RST" /\ network[p] # <<>>
            BY <5>3, <5>1, <5>2, <5>1a DEF LastMsg
          <5>5. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>4 DEF Aux_RST_at_end
          <5>. QED  BY <4>0, <5>5
        <4>2. CASE p # local
          <5>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
            BY <4>2 DEF LastMsg
          <5>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>1 DEF Aux_RST_at_end
          <5>. QED  BY <4>0, <5>2
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  (*************************************************************************)
  (* Listen: Tail+Append (consume "SYN" from n[local], append "SYN,ACK"   *)
  (* to n[remote]).  Local LISTEN -> SR.                                  *)
  (*************************************************************************)
  <1>13. CASE Listen(local, remote)
    <2>. USE <1>13 DEF Listen
    <2>. /\ network' = [network EXCEPT ![remote] = Append(@, "SYN,ACK"),
                                       ![local]  = Tail(network[local])]
         /\ connstate' = [connstate EXCEPT ![local] = "SYN-RECEIVED"]
         /\ connstate'[local] = "SYN-RECEIVED"
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ network'[remote] = Append(network[remote], "SYN,ACK")
         /\ network'[local] = Tail(network[local])
         /\ \A r \in Peers : r # local /\ r # remote => network'[r] = network[r]
         /\ connstate[local] = "LISTEN"
         /\ IsPrefix(<<"SYN">>, network[local])
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>head. /\ network[local] # <<>>
             /\ Head(network[local]) = "SYN"
             /\ Tail(network[local]) \in Seq(Msgs)
      BY PrefixOneNonEmpty DEF TypeOK, Msgs
    <2>tail. /\ Len(network'[local]) = Len(network[local]) - 1
             /\ Len(network[local]) >= 1
             /\ \A i \in 1..Len(network'[local]) : network'[local][i] = network[local][i + 1]
      BY <2>head DEF TypeOK, Msgs
    <2>1. Inv'
      \* network'[remote] = Append, never empty.  So {p : n'[p] = <<>>} \subseteq {local}.
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>1. l # remote /\ r # remote
        BY DEF TypeOK, Msgs
      <3>2. l = local /\ r = local
        BY <3>1, PeersAB
      <3>. QED  BY <3>2
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. q # remote
        \* n'[remote] = Append != <<>>.
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "SYN,ACK") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "SYN-RECEIVED"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "SYN,ACK") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      \* But connstate'[q] = "SYN-RECEIVED" # "ESTABLISHED", so we need to derive
      \* a contradiction with the aux LHS (which requires post connstate[q] = EST).
      \* Use the fact that p # q with PeersAB to force p = remote, then the
      \* head of n'[p] is the appended "SYN,ACK", not "ACK".  But network'[p]
      \* = <<"ACK">> (just the singleton).  Append(n[remote], "SYN,ACK")
      \* has last element "SYN,ACK", not "ACK".  Length 1 means n[remote]
      \* was <<>>, post Append(<<>>, "SYN,ACK") = <<"SYN,ACK">> # <<"ACK">>.
      <3>3. p = remote
        BY <3>2, PeersAB
      <3>4. network'[p] = Append(network[p], "SYN,ACK")
        BY <3>3
      <3>. SUFFICES Append(network[p], "SYN,ACK") = <<"ACK">> => FALSE
        BY <3>4
      <3>. network[p] \in Seq(Msgs)
        BY DEF TypeOK, Msgs
      <3>. QED  OBVIOUS
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "SYN,ACK") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "SYN-RECEIVED"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local
        \* connstate'[local] = SR # EST.
        BY DEF TypeOK
      <3>2. q = local
        BY <3>1, PeersAB
      <3>3. p = remote
        BY <3>1, PeersAB
      \* HasMsg("SYN,ACK", p)' = HasMsg("SYN,ACK", remote)'.  network'[remote] =
      \* Append(network[remote], "SYN,ACK") so SYN,ACK is at the end.  ✓.
      <3>4. network[p] \in Seq(Msgs) /\ Len(network[p]) \in Nat
        BY DEF TypeOK, Msgs
      <3>5. network'[p] = Append(network[p], "SYN,ACK")
        BY <3>3
      <3>6. Len(network'[p]) = Len(network[p]) + 1
            /\ network'[p][Len(network'[p])] = "SYN,ACK"
        BY <3>4, <3>5
      <3>7. \E i \in 1..Len(network'[p]) : network'[p][i] = "SYN,ACK"
        BY <3>6
      <3>. QED  BY <3>7 DEF HasMsg
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE p = remote
        \* p = remote, q = local (with PeersAB).  q post = SR -> LastMsg = SYN,ACK.
        <4>1. q = local /\ q # remote
          BY <3>1, PeersAB
        <4>2. connstate'[q] = "SYN-RECEIVED"
          BY <4>1
        <4>3. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>4. network'[p] = Append(network[p], "SYN,ACK")
          BY <3>1
        <4>5. LastMsg(p)' = "SYN,ACK"
          BY <4>3, <4>4 DEF LastMsg
        <4>. QED  BY <4>2, <4>5
      <3>2. CASE p = local
        \* p = local: LastMsg(p)' = LastMsg(p) when Len >= 2; vacuous when Len = 1
        \* (since post Tail = <<>>).  q = remote, connstate'[q] = connstate[q].
        <4>0. q # local /\ q = remote
          BY <3>2, PeersAB
        <4>1. network'[p] = Tail(network[p]) /\ network[p] \in Seq(Msgs)
              /\ network'[p] \in Seq(Msgs) /\ network'[p] # <<>>
          BY <3>2 DEF TypeOK, Msgs
        <4>2. Len(network'[p]) >= 1
          BY <4>1, EmptySeq
        <4>3. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
          BY <3>2, <2>tail
        <4>3a. Len(network[p]) >= 2
          BY <4>3, <4>2
        <4>4. network'[p][Len(network'[p])] = network[p][Len(network[p])]
          BY <3>2, <2>tail, <4>3, <4>3a
        <4>5. LastMsg(p)' = LastMsg(p)
          BY <4>4, <4>3, <4>2 DEF LastMsg
        <4>6. network[p] # <<>>
          BY <4>3a
        <4>7. connstate'[q] = connstate[q]
          BY <4>0 DEF TypeOK
        <4>. QED  BY <4>5, <4>6, <4>7 DEF Aux_LastMsg
      <3>3. CASE p # remote /\ p # local
        \* In 2-peer setup, this is impossible.
        BY <3>3, PeersAB
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE p = remote
        \* LastMsg(p)' = "SYN,ACK" # "RST" -- vacuous.
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. LastMsg(p)' = "SYN,ACK"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p = local
        <4>0. q # local /\ q = remote
          BY <3>2, PeersAB
        <4>1. network'[p] = Tail(network[p]) /\ network[p] \in Seq(Msgs)
              /\ network'[p] \in Seq(Msgs)
          BY <3>2 DEF TypeOK, Msgs
        <4>2. Len(network'[p]) >= 1
          BY <4>1, EmptySeq
        <4>3. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
          BY <3>2, <2>tail
        <4>3a. Len(network[p]) >= 2
          BY <4>3, <4>2
        <4>4. network'[p][Len(network'[p])] = network[p][Len(network[p])]
          BY <3>2, <2>tail, <4>3, <4>3a
        <4>5. LastMsg(p)' = LastMsg(p) /\ LastMsg(p) = "RST" /\ network[p] # <<>>
          BY <4>4, <4>3, <4>2, <4>3a DEF LastMsg
        <4>6. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
          BY <4>5 DEF Aux_RST_at_end
        <4>7. connstate'[q] = connstate[q]
          BY <4>0 DEF TypeOK
        <4>. QED  BY <4>6, <4>7
      <3>3. CASE p # remote /\ p # local
        BY <3>3, PeersAB
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  (*************************************************************************)
  (* Established: Tail "FIN" from n[local], Append "ACKofFIN" to          *)
  (* n[remote].  Local EST -> CW.  Same shape as Listen.                  *)
  (*************************************************************************)
  <1>14. CASE Established(local, remote)
    <2>. USE <1>14 DEF Established
    <2>. /\ network' = [network EXCEPT ![remote] = Append(@, "ACKofFIN"),
                                       ![local]  = Tail(network[local])]
         /\ connstate' = [connstate EXCEPT ![local] = "CLOSE-WAIT"]
         /\ connstate'[local] = "CLOSE-WAIT"
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ network'[remote] = Append(network[remote], "ACKofFIN")
         /\ network'[local] = Tail(network[local])
         /\ \A r \in Peers : r # local /\ r # remote => network'[r] = network[r]
         /\ connstate[local] = "ESTABLISHED"
         /\ IsPrefix(<<"FIN">>, network[local])
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>head. /\ network[local] # <<>>
             /\ Head(network[local]) = "FIN"
             /\ Tail(network[local]) \in Seq(Msgs)
      BY PrefixOneNonEmpty DEF TypeOK, Msgs
    <2>tail. /\ Len(network'[local]) = Len(network[local]) - 1
             /\ Len(network[local]) >= 1
             /\ \A i \in 1..Len(network'[local]) : network'[local][i] = network[local][i + 1]
      BY <2>head DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>1. l # remote /\ r # remote
        BY DEF TypeOK, Msgs
      <3>2. l = local /\ r = local
        BY <3>1, PeersAB
      <3>. QED  BY <3>2
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "ACKofFIN") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "CLOSE-WAIT"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "ACKofFIN") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>3. p = remote
        BY <3>2, PeersAB
      <3>4. network'[p] = Append(network[p], "ACKofFIN")
        BY <3>3
      <3>. SUFFICES Append(network[p], "ACKofFIN") = <<"ACK">> => FALSE
        BY <3>4
      <3>. network[p] \in Seq(Msgs)
        BY DEF TypeOK, Msgs
      <3>. QED  OBVIOUS
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "ACKofFIN") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "CLOSE-WAIT"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local
        BY DEF TypeOK
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "CLOSE-WAIT"
        BY <3>2
      <3>. QED  BY DEF PostEst, PostEstStrict
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE p = remote
        <4>1. q = local /\ q # remote
          BY <3>1, PeersAB
        <4>2. connstate'[q] = "CLOSE-WAIT"
          BY <4>1
        <4>3. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>4. network'[p] = Append(network[p], "ACKofFIN")
          BY <3>1
        <4>5. LastMsg(p)' = "ACKofFIN"
          BY <4>3, <4>4 DEF LastMsg
        <4>. QED  BY <4>2, <4>5
      <3>2. CASE p = local
        <4>0. q # local /\ q = remote
          BY <3>2, PeersAB
        <4>1. network'[p] = Tail(network[p]) /\ network[p] \in Seq(Msgs)
              /\ network'[p] \in Seq(Msgs) /\ network'[p] # <<>>
          BY <3>2 DEF TypeOK, Msgs
        <4>2. Len(network'[p]) >= 1
          BY <4>1, EmptySeq
        <4>3. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
          BY <3>2, <2>tail
        <4>3a. Len(network[p]) >= 2
          BY <4>3, <4>2
        <4>4. network'[p][Len(network'[p])] = network[p][Len(network[p])]
          BY <3>2, <2>tail, <4>3, <4>3a
        <4>5. LastMsg(p)' = LastMsg(p)
          BY <4>4, <4>3, <4>2 DEF LastMsg
        <4>6. network[p] # <<>>
          BY <4>3a
        <4>7. connstate'[q] = connstate[q]
          BY <4>0 DEF TypeOK
        <4>. QED  BY <4>5, <4>6, <4>7 DEF Aux_LastMsg
      <3>3. CASE p # remote /\ p # local
        BY <3>3, PeersAB
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE p = remote
        <4>. network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. LastMsg(p)' = "ACKofFIN"
          BY <3>1 DEF LastMsg
        <4>. QED  OBVIOUS
      <3>2. CASE p = local
        <4>0. q # local /\ q = remote
          BY <3>2, PeersAB
        <4>1. network'[p] = Tail(network[p]) /\ network[p] \in Seq(Msgs)
              /\ network'[p] \in Seq(Msgs)
          BY <3>2 DEF TypeOK, Msgs
        <4>2. Len(network'[p]) >= 1
          BY <4>1, EmptySeq
        <4>3. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
          BY <3>2, <2>tail
        <4>3a. Len(network[p]) >= 2
          BY <4>3, <4>2
        <4>4. network'[p][Len(network'[p])] = network[p][Len(network[p])]
          BY <3>2, <2>tail, <4>3, <4>3a
        <4>5. LastMsg(p)' = LastMsg(p) /\ LastMsg(p) = "RST" /\ network[p] # <<>>
          BY <4>4, <4>3, <4>2, <4>3a DEF LastMsg
        <4>6. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
          BY <4>5 DEF Aux_RST_at_end
        <4>7. connstate'[q] = connstate[q]
          BY <4>0 DEF TypeOK
        <4>. QED  BY <4>6, <4>7
      <3>3. CASE p # remote /\ p # local
        BY <3>3, PeersAB
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  (*************************************************************************)
  (* FinWait2: Tail "FIN" from n[local], Append "ACKofFIN" to n[remote].  *)
  (* Local FW2 -> TW.  Same shape as Established/Listen.                  *)
  (*************************************************************************)
  <1>15. CASE FinWait2(local, remote)
    <2>. USE <1>15 DEF FinWait2
    <2>. /\ network' = [network EXCEPT ![remote] = Append(@, "ACKofFIN"),
                                       ![local]  = Tail(network[local])]
         /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]
         /\ connstate'[local] = "TIME-WAIT"
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ network'[remote] = Append(network[remote], "ACKofFIN")
         /\ network'[local] = Tail(network[local])
         /\ \A r \in Peers : r # local /\ r # remote => network'[r] = network[r]
         /\ connstate[local] = "FIN-WAIT-2"
         /\ IsPrefix(<<"FIN">>, network[local])
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>head. /\ network[local] # <<>>
             /\ Head(network[local]) = "FIN"
             /\ Tail(network[local]) \in Seq(Msgs)
      BY PrefixOneNonEmpty DEF TypeOK, Msgs
    <2>tail. /\ Len(network'[local]) = Len(network[local]) - 1
             /\ Len(network[local]) >= 1
             /\ \A i \in 1..Len(network'[local]) : network'[local][i] = network[local][i + 1]
      BY <2>head DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>1. l # remote /\ r # remote
        BY DEF TypeOK, Msgs
      <3>2. l = local /\ r = local
        BY <3>1, PeersAB
      <3>. QED  BY <3>2
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "ACKofFIN") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "TIME-WAIT"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "ACKofFIN") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>3. p = remote
        BY <3>2, PeersAB
      <3>4. network'[p] = Append(network[p], "ACKofFIN")
        BY <3>3
      <3>. SUFFICES Append(network[p], "ACKofFIN") = <<"ACK">> => FALSE
        BY <3>4
      <3>. network[p] \in Seq(Msgs)
        BY DEF TypeOK, Msgs
      <3>. QED  OBVIOUS
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "ACKofFIN") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "TIME-WAIT"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local
        BY DEF TypeOK
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "TIME-WAIT"
        BY <3>2
      <3>. QED  BY DEF PostEst, PostEstStrict
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE p = remote
        \* q = local post = TW, not in covered states.  Vacuous.
        <4>. q = local /\ q # remote
          BY <3>1, PeersAB
        <4>. connstate'[q] = "TIME-WAIT"
          OBVIOUS
        <4>. QED  OBVIOUS
      <3>2. CASE p = local
        <4>0. q # local /\ q = remote
          BY <3>2, PeersAB
        <4>1. network'[p] = Tail(network[p]) /\ network[p] \in Seq(Msgs)
              /\ network'[p] \in Seq(Msgs) /\ network'[p] # <<>>
          BY <3>2 DEF TypeOK, Msgs
        <4>2. Len(network'[p]) >= 1
          BY <4>1, EmptySeq
        <4>3. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
          BY <3>2, <2>tail
        <4>3a. Len(network[p]) >= 2
          BY <4>3, <4>2
        <4>4. network'[p][Len(network'[p])] = network[p][Len(network[p])]
          BY <3>2, <2>tail, <4>3, <4>3a
        <4>5. LastMsg(p)' = LastMsg(p)
          BY <4>4, <4>3, <4>2 DEF LastMsg
        <4>6. network[p] # <<>>
          BY <4>3a
        <4>7. connstate'[q] = connstate[q]
          BY <4>0 DEF TypeOK
        <4>. QED  BY <4>5, <4>6, <4>7 DEF Aux_LastMsg
      <3>3. CASE p # remote /\ p # local
        BY <3>3, PeersAB
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE p = remote
        \* q = local post = TW \in {TW, CLOSED, LISTEN}.
        <4>. q = local /\ q # remote
          BY <3>1, PeersAB
        <4>. connstate'[q] = "TIME-WAIT"
          OBVIOUS
        <4>. QED  OBVIOUS
      <3>2. CASE p = local
        <4>0. q # local /\ q = remote
          BY <3>2, PeersAB
        <4>1. network'[p] = Tail(network[p]) /\ network[p] \in Seq(Msgs)
              /\ network'[p] \in Seq(Msgs)
          BY <3>2 DEF TypeOK, Msgs
        <4>2. Len(network'[p]) >= 1
          BY <4>1, EmptySeq
        <4>3. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
          BY <3>2, <2>tail
        <4>3a. Len(network[p]) >= 2
          BY <4>3, <4>2
        <4>4. network'[p][Len(network'[p])] = network[p][Len(network[p])]
          BY <3>2, <2>tail, <4>3, <4>3a
        <4>5. LastMsg(p)' = LastMsg(p) /\ LastMsg(p) = "RST" /\ network[p] # <<>>
          BY <4>4, <4>3, <4>2, <4>3a DEF LastMsg
        <4>6. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
          BY <4>5 DEF Aux_RST_at_end
        <4>7. connstate'[q] = connstate[q]
          BY <4>0 DEF TypeOK
        <4>. QED  BY <4>6, <4>7
      <3>3. CASE p # remote /\ p # local
        BY <3>3, PeersAB
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  (*************************************************************************)
  (* Note2: pre n[local] = <<"FIN","ACKofFIN">> ++ rest,                    *)
  (*        n'[local] = SubSeq(n[local], 3, Len(n[local])),                 *)
  (*        n'[remote] = Append(n[remote], "ACKofFIN"),                     *)
  (*        local FW1 -> TW.                                                 *)
  (*************************************************************************)
  <1>16. CASE Note2(local, remote)
    <2>. USE <1>16 DEF Note2
    <2>. /\ network' = [network EXCEPT ![remote] = Append(@, "ACKofFIN"),
                                       ![local]  = SubSeq(network[local], 3, Len(network[local]))]
         /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]
         /\ connstate'[local] = "TIME-WAIT"
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ network'[remote] = Append(network[remote], "ACKofFIN")
         /\ network'[local] = SubSeq(network[local], 3, Len(network[local]))
         /\ \A r \in Peers : r # local /\ r # remote => network'[r] = network[r]
         /\ connstate[local] = "FIN-WAIT-1"
         /\ IsPrefix(<<"FIN", "ACKofFIN">>, network[local])
         /\ local # remote
      BY DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>head. /\ Len(network[local]) >= 2
             /\ network[local][1] = "FIN"
             /\ network[local][2] = "ACKofFIN"
             /\ network[local] # <<>>
      BY PrefixTwoNonEmpty DEF TypeOK, Msgs
    <2>sub. /\ Len(network'[local]) = Len(network[local]) - 2
            /\ \A i \in 1..Len(network'[local]) : network'[local][i] = network[local][i + 2]
            /\ network'[local] \in Seq(Msgs)
      <3>1. SubSeq(network[local], 3, Len(network[local])) \in Seq(Msgs)
        BY <2>head, SubSeqProperties DEF TypeOK, Msgs
      <3>2. Len(SubSeq(network[local], 3, Len(network[local])))
            = Len(network[local]) - 3 + 1
        BY <2>head, SubSeqProperties DEF TypeOK, Msgs
      <3>3. \A i \in 1..(Len(network[local]) - 3 + 1) :
              SubSeq(network[local], 3, Len(network[local]))[i]
                = network[local][i + 3 - 1]
        BY <2>head, SubSeqProperties DEF TypeOK, Msgs
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>1. l # remote /\ r # remote
        BY DEF TypeOK, Msgs
      <3>2. l = local /\ r = local
        BY <3>1, PeersAB
      <3>. connstate'[l] = "TIME-WAIT" /\ connstate'[r] = "TIME-WAIT"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "ACKofFIN") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "TIME-WAIT"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "ACKofFIN") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "TIME-WAIT"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. q # remote
        <4>. SUFFICES ASSUME q = remote PROVE FALSE
          OBVIOUS
        <4>. network'[q] = Append(network[q], "ACKofFIN") /\ network[q] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "TIME-WAIT"
        BY <3>2
      <3>. QED  OBVIOUS
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local
        BY DEF TypeOK
      <3>2. q = local
        BY <3>1, PeersAB
      <3>. connstate'[q] = "TIME-WAIT"
        BY <3>2
      <3>. QED  BY DEF PostEst, PostEstStrict
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE q = local
        \* q = local post = TW, not in covered states. Vacuous.
        BY <3>1
      <3>2. CASE q # local
        <4>0. connstate'[q] = connstate[q] /\ q = remote
          BY <3>2, PeersAB DEF TypeOK
        <4>1. CASE p = remote
          BY <4>0, <3>2, <4>1
        <4>2. CASE p = local
          <5>0. network'[p] = SubSeq(network[p], 3, Len(network[p]))
                /\ network[p] \in Seq(Msgs)
                /\ network'[p] \in Seq(Msgs)
                /\ network'[p] # <<>>
                /\ Len(network[p]) >= 2
            BY <4>2 DEF TypeOK, Msgs
          <5>1. Len(network'[p]) >= 1
            BY <5>0, EmptySeq
          <5>2. Len(network'[p]) = Len(network[p]) - 2
            BY <4>2, <2>sub
          <5>3. Len(network[p]) >= 3
            BY <5>2, <5>1
          <5>4. \A i \in 1..Len(network'[p]) : network'[p][i] = network[p][i + 2]
            BY <4>2, <2>sub
          <5>5. network'[p][Len(network'[p])] = network[p][Len(network[p])]
            BY <5>1, <5>2, <5>3, <5>4
          <5>6. LastMsg(p)' = LastMsg(p)
            BY <5>5, <5>1, <5>2 DEF LastMsg
          <5>7. network[p] # <<>>
            BY <5>3
          <5>. QED  BY <4>0, <5>6, <5>7 DEF Aux_LastMsg
        <4>3. CASE p # local /\ p # remote
          BY <4>3, PeersAB
        <4>. QED  BY <4>1, <4>2, <4>3
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE q = local
        \* q = local post = TW \in {TW, CLOSED, LISTEN}.
        BY <3>1
      <3>2. CASE q # local
        <4>0. connstate'[q] = connstate[q] /\ q = remote
          BY <3>2, PeersAB DEF TypeOK
        <4>1. CASE p = remote
          BY <4>0, <3>2, <4>1
        <4>2. CASE p = local
          <5>0. network'[p] = SubSeq(network[p], 3, Len(network[p]))
                /\ network[p] \in Seq(Msgs)
                /\ network'[p] \in Seq(Msgs)
                /\ network'[p] # <<>>
                /\ Len(network[p]) >= 2
            BY <4>2 DEF TypeOK, Msgs
          <5>1. Len(network'[p]) >= 1
            BY <5>0, EmptySeq
          <5>2. Len(network'[p]) = Len(network[p]) - 2
            BY <4>2, <2>sub
          <5>3. Len(network[p]) >= 3
            BY <5>2, <5>1
          <5>4. \A i \in 1..Len(network'[p]) : network'[p][i] = network[p][i + 2]
            BY <4>2, <2>sub
          <5>5. network'[p][Len(network'[p])] = network[p][Len(network[p])]
            BY <5>1, <5>2, <5>3, <5>4
          <5>6. LastMsg(p)' = LastMsg(p) /\ LastMsg(p) = "RST"
            BY <5>5, <5>1, <5>2 DEF LastMsg
          <5>7. network[p] # <<>>
            BY <5>3
          <5>8. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>6, <5>7 DEF Aux_RST_at_end
          <5>. QED  BY <4>0, <5>8
        <4>3. CASE p # local /\ p # remote
          BY <4>3, PeersAB
        <4>. QED  BY <4>1, <4>2, <4>3
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  <1>r. CASE SynSent(local, remote) \/ SynReceived(local, remote)
              \/ FinWait1(local, remote)
    \* TODO: discharge the remaining 3 system action sub-cases.
    OMITTED
  <1>. QED  BY <1>9, <1>10, <1>11, <1>13, <1>14, <1>15, <1>16, <1>r

(***************************************************************************)
(* Reset action (Note3): two sub-cases.                                    *)
(*   - Note3 send: tcb[local], append "RST" to n[remote], local -> TW.    *)
(*   - Note3 RST receive: head=RST, Tail n[local], local -> LISTEN/CLOSED.*)
(***************************************************************************)
LEMMA IndInvReset ==
  ASSUME IndInv, TypeOK',
         NEW local \in Peers, NEW remote \in Peers,
         Note3(local, remote)
  PROVE  IndInv'
  <1>. USE PeersAB DEF IndInv
  <1>. local # remote
    BY DEF Note3
  <1>send. CASE /\ tcb[local]
                /\ network' = [network EXCEPT ![remote] = Append(@, "RST")]
                /\ connstate' = [connstate EXCEPT ![local] = "TIME-WAIT"]
    <2>. /\ network'[remote] = Append(network[remote], "RST")
         /\ connstate'[local] = "TIME-WAIT"
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : r # remote => network'[r] = network[r]
      BY <1>send DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ l # remote /\ r # remote /\ network[l] = <<>> /\ network[r] = <<>>
        BY DEF TypeOK, Msgs
      <3>. l \in {p \in Peers : network[p] = <<>>}
           /\ r \in {p \in Peers : network[p] = <<>>}
        OBVIOUS
      <3>. connstate[l] = "ESTABLISHED" <=> connstate[r] = "ESTABLISHED"
        BY DEF Inv
      <3>. /\ (l = local => connstate'[l] = "TIME-WAIT")
           /\ (r = local => connstate'[r] = "TIME-WAIT")
        OBVIOUS
      <3>. QED  OBVIOUS
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. CASE p = remote
        \* network'[p] = Append(n[p], "RST") = <<"RST">>: pre n[p] = <<>>.
        <4>1. q # remote /\ q = local
          BY <3>1, PeersAB
        \* connstate'[q] = TIME-WAIT # ESTABLISHED.
        <4>2. connstate'[q] = "TIME-WAIT"
          BY <4>1
        <4>. QED  BY <4>2
      <3>2. CASE p # remote
        \* network'[p] = network[p].  q = remote, network'[q] = Append # <<>>.
        <4>. SUFFICES ASSUME network'[q] = <<>> PROVE FALSE
          OBVIOUS
        <4>1. q = remote
          BY <3>2, PeersAB
        <4>2. network'[q] = Append(network[q], "RST")
          BY <4>1
        <4>. QED  BY <4>2 DEF TypeOK, Msgs
      <3>. QED  BY <3>1, <3>2
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. p # remote
        \* If p = remote, network'[p] = Append(n[p], "RST") never = <<"ACK">>.
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "RST") = <<"ACK">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>3. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  BY <3>3
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. p # remote
        <4>. SUFFICES ASSUME p = remote PROVE FALSE
          OBVIOUS
        <4>. Append(network[p], "RST") = <<"ACKofFIN">> /\ network[p] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>. QED  OBVIOUS
      <3>2. q # remote /\ network[q] = <<>>
        OBVIOUS
      <3>3. p = local /\ q = local
        BY <3>1, <3>2, PeersAB
      <3>. QED  BY <3>3
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local
        \* connstate'[local] = TW # EST.
        BY DEF TypeOK
      <3>2. q = local
        BY <3>1, PeersAB
      \* q = local post = TW \in PostEst.
      <3>. connstate'[q] = "TIME-WAIT"
        BY <3>2
      <3>. QED  BY DEF PostEst, PostEstStrict
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE p = remote
        \* p = remote: LastMsg(p)' = "RST".  connstate'[q] = q's pre state if
        \* q != local, or TW if q = local.  TW not in covered states.  For
        \* q != local: q = local? No, q # local since q # p = remote and p =
        \* remote means q = local (with PeersAB).
        <4>. q # remote /\ q = local
          BY <3>1, PeersAB
        <4>. connstate'[q] = "TIME-WAIT"
          OBVIOUS
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. q # local
          \* If q = local, connstate'[q] = TW, not covered.  Otherwise q # local
          \* and connstate'[q] = connstate[q].
          BY <3>2, PeersAB
        <4>3. connstate'[q] = connstate[q]
          BY <4>2 DEF TypeOK
        <4>. QED
          BY <4>1, <4>3 DEF Aux_LastMsg
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE p = remote
        <4>. q # remote /\ q = local
          BY <3>1, PeersAB
        <4>. connstate'[q] = "TIME-WAIT"
          OBVIOUS
        <4>. QED  OBVIOUS
      <3>2. CASE p # remote
        <4>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
          BY <3>2 DEF LastMsg
        <4>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
          BY <4>1 DEF Aux_RST_at_end
        <4>3. q # local
          BY <3>2, PeersAB
        <4>4. connstate'[q] = connstate[q]
          BY <4>3 DEF TypeOK
        <4>. QED  BY <4>2, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv

  <1>recv. CASE /\ IsPrefix(<<"RST">>, network[local])
                /\ network' = [network EXCEPT ![local] = Tail(network[local])]
                /\ \/ connstate' = [connstate EXCEPT ![local] = "LISTEN"]
                   \/ connstate' = [connstate EXCEPT ![local] = "CLOSED"]
    <2>. /\ network'[local] = Tail(network[local])
         /\ \A r \in Peers : r # local => connstate'[r] = connstate[r]
         /\ \A r \in Peers : r # local => network'[r] = network[r]
         /\ connstate'[local] \in {"LISTEN", "CLOSED"}
      BY <1>recv DEF TypeOK
    <2>. \A p \in Peers : network[p] \in Seq(Msgs)
      BY DEF TypeOK, Msgs
    <2>head. /\ network[local] # <<>>
             /\ Head(network[local]) = "RST"
             /\ Tail(network[local]) \in Seq(Msgs)
      BY <1>recv, PrefixOneNonEmpty DEF TypeOK, Msgs
    <2>tail. /\ Len(network'[local]) = Len(network[local]) - 1
             /\ Len(network[local]) >= 1
             /\ \A i \in 1..Len(network'[local]) : network'[local][i] = network[local][i + 1]
      BY <2>head DEF TypeOK, Msgs
    <2>headRST. network[local][1] = "RST"
      BY <2>head DEF TypeOK, Msgs
    <2>1. Inv'
      <3>. SUFFICES ASSUME NEW l \in {p \in Peers : network'[p] = <<>>},
                            NEW r \in {p \in Peers : network'[p] = <<>>}
                     PROVE  connstate'[l] = "ESTABLISHED" <=> connstate'[r] = "ESTABLISHED"
        BY DEF Inv
      <3>0. /\ network'[l] = <<>> /\ network'[r] = <<>>
            /\ (l # local => network[l] = network'[l])
            /\ (r # local => network[r] = network'[r])
            /\ (l = local => network[l] = <<"RST">>)
            /\ (r = local => network[r] = <<"RST">>)
        <4>. \A x \in Peers : x = local => network'[x] = Tail(network[x])
          OBVIOUS
        <4>. \A x \in Peers : (x = local /\ Tail(network[x]) = <<>>) =>
                   network[x] = <<"RST">>
          BY <2>head
        <4>. QED  OBVIOUS
      <3>1. CASE l # local /\ r # local
        <4>. network[l] = <<>> /\ network[r] = <<>>
          BY <3>0, <3>1
        <4>. l \in {p \in Peers : network[p] = <<>>}
             /\ r \in {p \in Peers : network[p] = <<>>}
          OBVIOUS
        <4>. connstate[l] = "ESTABLISHED" <=> connstate[r] = "ESTABLISHED"
          BY DEF Inv
        <4>. connstate'[l] = connstate[l] /\ connstate'[r] = connstate[r]
          BY <3>1 DEF TypeOK
        <4>. QED  OBVIOUS
      <3>2. CASE l = local
        <4>1. connstate'[l] \in {"LISTEN", "CLOSED"} /\ connstate'[l] # "ESTABLISHED"
          BY <3>2
        <4>2. CASE r = local
          BY <3>2, <4>2, <4>1
        <4>3. CASE r # local
          <5>1. network[r] = <<>>
            BY <3>0, <4>3
          <5>2. network[local] = <<"RST">> /\ local \in Peers /\ r \in Peers /\ local # r
            BY <3>2, <3>0, <4>3
          <5>3. connstate[r] # "ESTABLISHED"
            BY <5>1, <5>2 DEF Aux_singleton_RST
          <5>4. connstate'[r] = connstate[r]
            BY <4>3 DEF TypeOK
          <5>. QED  BY <4>1, <5>3, <5>4
        <4>. QED  BY <4>2, <4>3
      <3>3. CASE r = local /\ l # local
        <4>1. connstate'[r] \in {"LISTEN", "CLOSED"} /\ connstate'[r] # "ESTABLISHED"
          BY <3>3
        <4>2. network[l] = <<>> /\ network[local] = <<"RST">>
              /\ local \in Peers /\ l \in Peers /\ local # l
          BY <3>0, <3>3
        <4>3. connstate[l] # "ESTABLISHED"
          BY <4>2 DEF Aux_singleton_RST
        <4>4. connstate'[l] = connstate[l]
          BY <3>3 DEF TypeOK
        <4>. QED  BY <4>1, <4>3, <4>4
      <3>. QED  BY <3>1, <3>2, <3>3
    <2>2. Aux_singleton_RST'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"RST">>, network'[q] = <<>>
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_RST
      <3>1. CASE q = local
        \* connstate'[q] in {LISTEN, CLOSED}, both # EST.
        BY <3>1
      <3>2. CASE q # local
        <4>1. connstate'[q] = connstate[q]
          BY <3>2 DEF TypeOK
        <4>2. network[q] = <<>>
          BY <3>2
        <4>3. CASE p = local
          <5>0. Tail(network[p]) = <<"RST">>
            BY <4>3
          <5>0a. Head(network[p]) = "RST" /\ network[p] # <<>>
                /\ network[p] \in Seq(Msgs)
            BY <4>3, <2>head DEF TypeOK, Msgs
          <5>0b. Len(Tail(network[p])) = 1 /\ Len(network[p]) >= 1
            BY <5>0, <5>0a, EmptySeq
          <5>0c. Len(network[p]) = 2
            BY <5>0a, <5>0b
          <5>0d. network[p] = <<network[p][1], network[p][2]>>
            BY <5>0a, <5>0c DEF TypeOK, Msgs
          <5>0e. network[p][1] = "RST"
            BY <5>0a DEF TypeOK, Msgs
          <5>0f. Tail(network[p]) = <<network[p][2]>>
            BY <5>0a, <5>0c DEF TypeOK, Msgs
          <5>0g. network[p][2] = "RST"
            BY <5>0, <5>0f
          <5>1. network[p] = <<"RST", "RST">>
            BY <5>0d, <5>0e, <5>0g
          <5>2. LastMsg(p) = "RST" /\ network[p] # <<>>
            BY <5>1 DEF LastMsg
          <5>3. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>2 DEF Aux_RST_at_end
          <5>. QED  BY <4>1, <5>3
        <4>4. CASE p # local
          <5>1. network[p] = <<"RST">>
            BY <4>4
          <5>. QED
            BY <4>1, <5>1, <4>2 DEF Aux_singleton_RST
        <4>. QED  BY <4>3, <4>4
      <3>. QED  BY <3>1, <3>2
    <2>3. Aux_singleton_ACK'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACK">>, network'[q] = <<>>,
                            connstate'[p] = "SYN-RECEIVED"
                     PROVE  connstate'[q] = "ESTABLISHED"
        BY DEF Aux_singleton_ACK
      <3>1. p # local
        \* connstate'[local] in {LISTEN, CLOSED} # SR.
        BY DEF TypeOK
      <3>2. connstate[p] = "SYN-RECEIVED"
        BY <3>1 DEF TypeOK
      <3>3. network'[p] = network[p] /\ network[p] = <<"ACK">>
        BY <3>1
      <3>4. CASE q = local
        \* By Aux_LastMsg pre with q' = p = remote SR: LastMsg(other) = SYN,ACK.
        \* But network[other] = network[local] # <<>> with head = "RST".
        \* In the q' = p sense, "p = SR" is the state-bearing peer; the
        \* aux says LastMsg(other where other # p) = SYN,ACK.
        \* other = local.  network[local] starts with RST.  LastMsg might be
        \* something else (last element). Let me think...
        \* Actually by Aux_LastMsg with q = p = remote in SR:
        \*   network[local] # <<>> => LastMsg(local) = "SYN,ACK".
        \* But network[local] head = "RST".  If Len = 1, LastMsg = "RST"
        \* # "SYN,ACK". Contradiction.  If Len >= 2, LastMsg is some other
        \* message; aux says it's SYN,ACK.  No direct contradiction.
        \* Better: use Aux_RST_at_end? No, that's about LastMsg = RST.
        \* Use the singleton: if pre n[local] = <<RST>>, by Aux_singleton_RST
        \* with p' = local, q' = remote: connstate[remote] # EST.  But pre
        \* connstate[p = remote] = SR, not EST.  No contradiction.
        \*
        \* Hmm tricky. Let me think differently. We need to show
        \* connstate'[q] = EST.  q = local post in {LISTEN, CLOSED}, # EST.
        \* So we need to derive a contradiction with the aux LHS.
        \*
        \* network'[q] = Tail(network[local]) = <<>> means pre Len(n[local]) = 1.
        \* So n[local] = <<"RST">>.  And p = remote with network[remote] = <<"ACK">>.
        \* Pre Aux_LastMsg with q' = p = remote SR: LastMsg(local) = "SYN,ACK".
        \* But LastMsg(local) = "RST" # "SYN,ACK".  Contradiction.
        <5>1. network[local] = <<"RST">>
          <6>. Tail(network[local]) = <<>>
            BY <3>4
          <6>. Len(network[local]) = 1
            BY <2>head, <2>tail
          <6>. QED  BY <2>headRST DEF TypeOK, Msgs
        <5>2. LastMsg(local) = "RST"
          BY <5>1 DEF LastMsg
        <5>3. network[local] # <<>>
          BY <5>1
        <5>. QED
          BY <3>4, <3>2, <3>1, <5>2, <5>3 DEF Aux_LastMsg
      <3>5. CASE q # local
        <4>1. network'[q] = network[q]
          BY <3>5
        <4>2. connstate'[q] = connstate[q]
          BY <3>5 DEF TypeOK
        <4>3. network[p] = <<"ACK">> /\ network[q] = <<>>
          BY <3>3, <4>1
        <4>4. connstate[q] = "ESTABLISHED"
          BY <3>2, <4>3 DEF Aux_singleton_ACK
        <4>. QED  BY <4>2, <4>4
      <3>. QED  BY <3>4, <3>5
    <2>4. Aux_singleton_ACKofFIN'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] = <<"ACKofFIN">>, network'[q] = <<>>,
                            connstate'[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
                     PROVE  connstate'[q] # "ESTABLISHED"
        BY DEF Aux_singleton_ACKofFIN
      <3>1. p # local
        BY DEF TypeOK
      <3>2. connstate[p] \in {"FIN-WAIT-1", "CLOSING", "LAST-ACK"}
        BY <3>1 DEF TypeOK
      <3>3. CASE q = local
        BY <3>3
      <3>4. CASE q # local
        <4>1. network'[p] = network[p] /\ network'[q] = network[q]
          BY <3>1, <3>4
        <4>2. connstate'[q] = connstate[q]
          BY <3>4 DEF TypeOK
        <4>3. network[p] = <<"ACKofFIN">> /\ network[q] = <<>>
          BY <4>1
        <4>. QED  BY <3>2, <4>2, <4>3 DEF Aux_singleton_ACKofFIN
      <3>. QED  BY <3>3, <3>4
    <2>5. Aux_EST_evidence'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, connstate'[p] = "ESTABLISHED"
                     PROVE  \/ connstate'[q] \in PostEst
                            \/ HasMsg("SYN", p)' \/ HasMsg("SYN", q)'
                            \/ HasMsg("ACK", q)' \/ HasMsg("ACK", p)'
                            \/ HasMsg("SYN,ACK", q)' \/ HasMsg("SYN,ACK", p)'
                            \/ HasMsg("FIN", p)' \/ HasMsg("FIN", q)'
                            \/ HasMsg("ACKofFIN", p)' \/ HasMsg("ACKofFIN", q)'
                            \/ HasMsg("RST", p)' \/ HasMsg("RST", q)'
        BY DEF Aux_EST_evidence
      <3>1. p # local /\ connstate[p] = "ESTABLISHED"
        BY DEF TypeOK
      <3>2. q = local
        BY <3>1, PeersAB
      \* Case-split on whether n[local] = <<"RST">> (singleton) or longer.
      <3>3. CASE network[local] = <<"RST">>
        \* Then by Aux_singleton_RST with p' = local, q' = remote: if
        \* network[remote] = <<>>, connstate[remote] # EST.  But
        \* connstate[remote] = connstate[p] = EST.  Contradiction with
        \* network[remote] = <<>>.  So network[remote] # <<>>.  Then there
        \* exists m \in Msgs in network[remote]; HasMsg(m, p)' for that m.
        <4>1. network[remote] # <<>>
          <5>. SUFFICES ASSUME network[remote] = <<>> PROVE FALSE
            OBVIOUS
          <5>1. local \in Peers /\ remote \in Peers /\ local # remote
            OBVIOUS
          <5>2. connstate[remote] # "ESTABLISHED"
            BY <3>3, <5>1 DEF Aux_singleton_RST
          <5>3. p = remote
            BY <3>1, <3>2, PeersAB
          <5>. QED  BY <3>1, <5>2, <5>3
        <4>2. p = remote
          BY <3>1, <3>2, PeersAB
        <4>3. network'[p] = network[p]
          BY <4>2
        <4>4. network[p] # <<>> /\ network[p] \in Seq(Msgs)
          BY <4>1, <4>2 DEF TypeOK, Msgs
        <4>5. network[p][1] \in Msgs /\ Len(network[p]) >= 1
              /\ Len(network[p]) \in Nat
          BY <4>4
        <4>6. Len(network'[p]) = Len(network[p]) /\ network'[p] = network[p]
          BY <4>3
        <4>7. Len(network'[p]) >= 1 /\ network'[p][1] = network[p][1]
              /\ Len(network'[p]) \in Nat
          BY <4>5, <4>6
        <4>8. 1 \in 1..Len(network'[p])
          BY <4>7
        <4>9. \E i \in 1..Len(network'[p]) : network'[p][i] \in Msgs
              /\ network'[p][i] = network[p][1]
          BY <4>5, <4>7, <4>8
        <4>. QED
          BY <4>5, <4>9 DEF HasMsg, Msgs
      <3>4. CASE Len(network[local]) >= 2
        \* network'[local] = Tail has at least one element.  HasMsg(X, local)'
        \* for X = network'[local][1] \in Msgs.
        <4>1. Len(network'[local]) = Len(network[local]) - 1 /\ Len(network'[local]) >= 1
          BY <3>4, <2>tail
        <4>2. network'[local] \in Seq(Msgs)
          BY DEF TypeOK, Msgs
        <4>3. network'[local][1] \in Msgs
          BY <4>1, <4>2
        <4>4. \E i \in 1..Len(network'[local]) : network'[local][i] = network'[local][1]
          BY <4>1
        <4>. QED  BY <3>2, <4>3, <4>4 DEF HasMsg, Msgs
      <3>5. \/ network[local] = <<"RST">> \/ Len(network[local]) >= 2
        <4>1. network[local] \in Seq(Msgs) /\ Len(network[local]) >= 1
          BY <2>head DEF TypeOK, Msgs
        <4>2. \/ Len(network[local]) = 1 \/ Len(network[local]) >= 2
          BY <4>1
        <4>3. CASE Len(network[local]) = 1
          \* network[local] = <<network[local][1]>> = <<"RST">>.
          <5>. network[local] = <<network[local][1]>>
            BY <4>3 DEF TypeOK, Msgs
          <5>. QED  BY <2>headRST
        <4>. QED  BY <4>2, <4>3
      <3>. QED  BY <3>3, <3>4, <3>5
    <2>6. Aux_LastMsg'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>
                     PROVE  /\ connstate'[q] = "SYN-RECEIVED"  => LastMsg(p)' = "SYN,ACK"
                            /\ connstate'[q] = "FIN-WAIT-1"    => LastMsg(p)' \in {"FIN", "RST"}
                            /\ connstate'[q] = "CLOSE-WAIT"    => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "LAST-ACK"      => LastMsg(p)' = "FIN"
                            /\ connstate'[q] = "CLOSING"       => LastMsg(p)' = "ACKofFIN"
                            /\ connstate'[q] = "SYN-SENT"      => LastMsg(p)' = "SYN"
        BY DEF Aux_LastMsg
      <3>1. CASE q = local
        \* connstate'[q] in {LISTEN, CLOSED}, neither in covered states.
        BY <3>1
      <3>2. CASE q # local
        <4>0. connstate'[q] = connstate[q]
          BY <3>2 DEF TypeOK
        <4>1. CASE p = local
          <5>0. network'[p] # <<>> /\ network'[p] = Tail(network[p])
                /\ network[p] \in Seq(Msgs)
                /\ network'[p] \in Seq(Msgs)
            BY <4>1 DEF TypeOK, Msgs
          <5>2. Len(network'[p]) >= 1
            BY <5>0, EmptySeq
          <5>1. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
            BY <4>1, <2>tail
          <5>1a. Len(network[p]) >= 2
            BY <5>1, <5>2
          <5>3. network'[p][Len(network'[p])] = network[p][Len(network[p])]
            BY <4>1, <2>tail, <5>1, <5>1a
          <5>4. LastMsg(p)' = LastMsg(p)
            BY <5>3, <5>1, <5>2 DEF LastMsg
          <5>5. network[p] # <<>>
            BY <5>1a
          <5>. QED  BY <4>0, <5>4, <5>5 DEF Aux_LastMsg
        <4>2. CASE p # local
          <5>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
            BY <4>2 DEF LastMsg
          <5>. QED  BY <4>0, <5>1 DEF Aux_LastMsg
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>2
    <2>7. Aux_RST_at_end'
      <3>. SUFFICES ASSUME NEW p \in Peers, NEW q \in Peers,
                            p # q, network'[p] # <<>>, LastMsg(p)' = "RST"
                     PROVE  connstate'[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
        BY DEF Aux_RST_at_end
      <3>1. CASE q = local
        BY <3>1
      <3>2. CASE q # local
        <4>0. connstate'[q] = connstate[q]
          BY <3>2 DEF TypeOK
        <4>1. CASE p = local
          <5>0. network'[p] # <<>> /\ network'[p] = Tail(network[p])
                /\ network[p] \in Seq(Msgs)
                /\ network'[p] \in Seq(Msgs)
            BY <4>1 DEF TypeOK, Msgs
          <5>2. Len(network'[p]) >= 1
            BY <5>0, EmptySeq
          <5>1. Len(network'[p]) = Len(network[p]) - 1 /\ Len(network[p]) >= 1
            BY <4>1, <2>tail
          <5>1a. Len(network[p]) >= 2
            BY <5>1, <5>2
          <5>3. network'[p][Len(network'[p])] = network[p][Len(network[p])]
            BY <4>1, <2>tail, <5>1, <5>1a
          <5>4. LastMsg(p)' = LastMsg(p) /\ LastMsg(p) = "RST" /\ network[p] # <<>>
            BY <5>3, <5>1, <5>2, <5>1a DEF LastMsg
          <5>5. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>4 DEF Aux_RST_at_end
          <5>. QED  BY <4>0, <5>5
        <4>2. CASE p # local
          <5>1. network'[p] = network[p] /\ LastMsg(p)' = LastMsg(p) /\ network[p] # <<>>
            BY <4>2 DEF LastMsg
          <5>2. connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}
            BY <5>1 DEF Aux_RST_at_end
          <5>. QED  BY <4>0, <5>2
        <4>. QED  BY <4>1, <4>2
      <3>. QED  BY <3>1, <3>2
    <2>. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF IndInv
  <1>. QED  BY <1>send, <1>recv DEF Note3

THEOREM IndInvIsInductive == IndInv /\ [Next]_vars => IndInv'
  <1>. SUFFICES ASSUME IndInv, [Next]_vars PROVE IndInv'
    OBVIOUS
  <1>. USE DEF IndInv
  <1>0. TypeOK'
    BY TypeOKInductive
  <1>stutter. CASE UNCHANGED vars
    BY <1>stutter, IndInvStutter
  <1>user. CASE User
    <2>. PICK local \in Peers, remote \in Peers :
            \/ ACTIVE_OPEN(local, remote)
            \/ PASSIVE_OPEN(local, remote)
            \/ CLOSE_SYN_SENT(local, remote)
            \/ CLOSE_SYN_RECEIVED(local, remote)
            \/ CLOSE_LISTEN(local, remote)
            \/ CLOSE_ESTABLISHED(local, remote)
            \/ CLOSE_CLOSE_WAIT(local, remote)
            \/ SEND(local, remote)
      BY <1>user DEF User
    <2>. QED  BY <1>0, IndInvUser
  <1>system. CASE System
    <2>. PICK local \in Peers, remote \in Peers :
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
      BY <1>system DEF System
    <2>. QED  BY <1>0, IndInvSystem
  <1>reset. CASE Reset
    <2>. PICK local \in Peers, remote \in Peers : Note3(local, remote)
      BY <1>reset DEF Reset
    <2>. QED  BY <1>0, IndInvReset
  <1>. QED  BY <1>stutter, <1>user, <1>system, <1>reset DEF Next

(***************************************************************************)
(* Once IndInvIsInductive is fully discharged, the main theorem follows: *)
(*                                                                         *)
(*   THEOREM SpecImpliesInv == Spec => []Inv                              *)
(*     <1>. QED BY IndInvInit, IndInvIsInductive, PTL DEF Spec, IndInv   *)
(***************************************************************************)
============================================================================
