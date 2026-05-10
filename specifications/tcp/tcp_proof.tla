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
  <1>2. CASE PASSIVE_OPEN(local, remote) \/ ACTIVE_OPEN(local, remote)
              \/ CLOSE_SYN_SENT(local, remote)
              \/ CLOSE_SYN_RECEIVED(local, remote)
              \/ CLOSE_LISTEN(local, remote)
              \/ CLOSE_ESTABLISHED(local, remote)
              \/ CLOSE_CLOSE_WAIT(local, remote)
              \/ SEND(local, remote)
    \* TODO: discharge the remaining 7 user-action sub-cases.
    OMITTED
  <1>. QED  BY <1>1, <1>2

THEOREM IndInvIsInductive == IndInv /\ [Next]_vars => IndInv'
  <1>. SUFFICES ASSUME IndInv, [Next]_vars PROVE IndInv'
    OBVIOUS
  <1>. USE DEF IndInv
  <1>0. TypeOK'
    BY TypeOKInductive
  <1>stutter. CASE UNCHANGED vars
    BY <1>stutter, IndInvStutter
  <1>next. CASE Next
    \* Per-action analysis -- to be filled in below.
    OMITTED
  <1>. QED  BY <1>stutter, <1>next

(***************************************************************************)
(* Once IndInvIsInductive is fully discharged, the main theorem follows: *)
(*                                                                         *)
(*   THEOREM SpecImpliesInv == Spec => []Inv                              *)
(*     <1>. QED BY IndInvInit, IndInvIsInductive, PTL DEF Spec, IndInv   *)
(***************************************************************************)
============================================================================
