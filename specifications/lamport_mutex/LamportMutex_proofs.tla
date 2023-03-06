------------------------ MODULE LamportMutex_proofs -------------------------
(***************************************************************************)
(* Proof of type correctness and safety of Lamport's distributed           *)
(* mutual-exclusion algorithm.                                             *)
(***************************************************************************)
EXTENDS LamportMutex, SequenceTheorems, TLAPS

USE DEF Clock

(***************************************************************************)
(* Proof of type correctness.                                              *)
(***************************************************************************)
LEMMA BroadcastType ==
  ASSUME network \in [Proc -> [Proc -> Seq(Message)]],
         NEW s \in Proc, NEW m \in Message
  PROVE  Broadcast(s,m) \in [Proc -> Seq(Message)]
BY AppendProperties DEF Broadcast

LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. ASSUME NEW p \in Proc,
               Request(p)
        PROVE  TypeOK'
    BY <2>1, BroadcastType, Zenon DEF Request, Message
  <2>2. ASSUME NEW p \in Proc,
               Enter(p)
        PROVE  TypeOK'
    BY <2>2 DEF Enter
  <2>3. ASSUME NEW p \in Proc,
               Exit(p)
        PROVE  TypeOK'
    BY <2>3, BroadcastType, Zenon DEF Exit, Message
  <2>4. ASSUME NEW p \in Proc,
               NEW q \in Proc \ {p},
               ReceiveRequest(p,q)
        PROVE  TypeOK'
    <3>. DEFINE m == Head(network[q][p])
                c == m.clock
    <3>1. /\ network[q][p] # << >>
          /\ m.type = "req"
          /\ req' = [req EXCEPT ![p][q] = c]
          /\ clock' = [clock EXCEPT ![p] = IF c > clock[p] THEN c + 1 ELSE @ + 1]
          /\ network' = [network EXCEPT ![q][p] = Tail(@),
                                        ![p][q] = Append(@, AckMessage)]
          /\ UNCHANGED <<ack, crit>>
      BY <2>4 DEF ReceiveRequest
    <3>2. m \in Message
      BY <3>1
    <3>3. m \in {ReqMessage(cc) : cc \in Clock}
      BY <3>1, <3>2 DEF Message, AckMessage, RelMessage
    <3>4. /\ clock' \in [Proc -> Clock]
          /\ req' \in [Proc -> [Proc -> Nat]]
      BY <3>1, <3>3 DEF ReqMessage
    <3>5. network' \in [Proc -> [Proc -> Seq(Message)]]
      <4>. DEFINE nw == [network EXCEPT ![q][p] = Tail(@)]
      <4>1. nw \in [Proc -> [Proc -> Seq(Message)]]
        BY <3>1
      <4>. HIDE DEF nw
      <4>2. AckMessage \in Message
        BY DEF Message
      <4>3. [nw EXCEPT ![p][q] = Append(@, AckMessage)] \in [Proc -> [Proc -> Seq(Message)]]
        BY <4>1, <4>2
      <4>. QED  BY <3>1, <4>3, Zenon DEF nw
    <3>6. /\ ack' \in [Proc -> SUBSET Proc]
          /\ crit' \in SUBSET Proc
      BY <3>1
    <3>. QED  BY <3>4, <3>5, <3>6, Zenon
  <2>5. ASSUME NEW p \in Proc,
               NEW q \in Proc \ {p},
               ReceiveAck(p,q)
        PROVE  TypeOK'
    BY <2>5 DEF ReceiveAck
  <2>6. ASSUME NEW p \in Proc,
               NEW q \in Proc \ {p},
               ReceiveRelease(p,q)
        PROVE  TypeOK'
    BY <2>6 DEF ReceiveRelease
  <2>7. CASE UNCHANGED vars
    BY <2>7 DEF vars
  <2>8. QED   BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Inductive invariants for the algorithm.                                 *)
(***************************************************************************)

(***************************************************************************)
(* We start the proof of safety by defining some auxiliary predicates:     *)
(* - Contains(s,mt) holds if channel s contains a message of type mt.      *)
(* - AtMostOne(s,mt) holds if channel s holds zero or one messages of      *)
(*   type mtype.                                                           *)
(* - Precedes(s,mt1,mt2) holds if in channel s, any message of type mt1    *)
(*   precedes any message of type mt2.                                     *)
(***************************************************************************)
Contains(s,mtype) == \E i \in 1 .. Len(s) : s[i].type = mtype
AtMostOne(s,mtype) == \A i,j \in 1 .. Len(s) :
  s[i].type = mtype /\ s[j].type = mtype => i = j
Precedes(s,mt1,mt2) == \A i,j \in 1 .. Len(s) :
  s[i].type = mt1 /\ s[j].type = mt2 => i < j

LEMMA NotContainsAtMostOne ==
  ASSUME NEW s \in Seq(Message), NEW mtype, ~ Contains(s,mtype)
  PROVE  AtMostOne(s, mtype)
BY DEF Contains, AtMostOne

LEMMA NotContainsPrecedes ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2, ~ Contains(s, mt2)
  PROVE  /\ Precedes(s, mt1, mt2)
         /\ Precedes(s, mt2, mt1)
BY DEF Contains, Precedes

LEMMA PrecedesHead ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2,
         s # << >>,
         Precedes(s,mt1,mt2), Head(s).type = mt2
  PROVE  ~ Contains(s,mt1)
BY DEF Precedes, Contains

LEMMA AtMostOneTail ==
  ASSUME NEW s \in Seq(Message), NEW mtype,
         s # << >>, AtMostOne(s, mtype)
  PROVE  AtMostOne(Tail(s), mtype)
BY DEF AtMostOne

LEMMA ContainsTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mtype, AtMostOne(s, mtype)
  PROVE  Contains(Tail(s), mtype) <=> Contains(s, mtype) /\ Head(s).type # mtype
BY DEF Contains, AtMostOne

LEMMA AtMostOneHead ==
  ASSUME NEW s \in Seq(Message), NEW mtype,
         AtMostOne(s,mtype), s # << >>, Head(s).type = mtype
  PROVE  ~ Contains(Tail(s), mtype)
<1>. SUFFICES ASSUME NEW i \in 1 .. Len(Tail(s)), Tail(s)[i].type = mtype
              PROVE  FALSE
  BY Tail(s) \in Seq(Message), Isa DEF Contains
<1>. QED  BY HeadTailProperties DEF AtMostOne

LEMMA ContainsSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, NEW m \in Message
  PROVE  Contains(Append(s,m), mtype) <=> m.type = mtype \/ Contains(s, mtype)
BY DEF Contains

LEMMA NotContainsSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, ~ Contains(s, mtype), NEW m \in Message
  PROVE  /\ AtMostOne(Append(s,m), mtype)
         /\ m.type # mtype => ~ Contains(Append(s,m), mtype)
BY DEF Contains, AtMostOne

LEMMA AtMostOneSend ==
  ASSUME NEW s \in Seq(Message), NEW mtype, AtMostOne(s, mtype), 
         NEW m \in Message, m.type # mtype
  PROVE  AtMostOne(Append(s,m), mtype)
BY DEF AtMostOne

LEMMA PrecedesSend ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2,
         NEW m \in Message, m.type # mt1
  PROVE  Precedes(Append(s,m), mt1, mt2) <=> Precedes(s, mt1, mt2)
BY DEF Precedes

LEMMA PrecedesTail ==
  ASSUME NEW s \in Seq(Message), NEW mt1, NEW mt2, Precedes(s, mt1, mt2)
  PROVE  Precedes(Tail(s), mt1, mt2)
BY DEF Precedes

LEMMA PrecedesInTail ==
  ASSUME NEW s \in Seq(Message), s # << >>,
         NEW mt1, NEW mt2, mt1 # mt2,
         Head(s).type = mt1 \/ Head(s).type \notin {mt1, mt2},
         Precedes(Tail(s), mt1, mt2)
  PROVE  Precedes(s, mt1, mt2)
BY SMTT(30) DEF Precedes

-----------------------------------------------------------------------------
(***************************************************************************)
(* In order to prove the safety property of the algorithm, we prove two    *)
(* inductive invariants. Our first invariant is itself a conjunction of    *)
(* two predicates:                                                         *)
(* - The first one states that each channel holds at most one message of   *)
(*   each type. Moreover, no process ever sends a message to itself.       *)
(* - The second predicate describes how request, acknowledgement, and      *)
(*   release messages are exchanged among processes, but does not refer to *)
(*   clock values held in the clock and req variables.                     *)
(***************************************************************************)

NetworkInv(p,q) ==
  LET s == network[p][q]
  IN  /\ AtMostOne(s,"req")
      /\ AtMostOne(s,"ack")
      /\ AtMostOne(s,"rel")
      /\ network[p][p] = << >>

CommInv(p) ==
  \/ /\ req[p][p] = 0 /\ ack[p] = {} /\ p \notin crit
     /\ \A q \in Proc : ~ Contains(network[p][q],"req") /\ ~ Contains(network[q][p],"ack")
  \/ /\ req[p][p] > 0 /\ p \in ack[p]
     /\ p \in crit => ack[p] = Proc
     /\ \A q \in Proc :
           LET pq == network[p][q]
               qp == network[q][p]
           IN  \/ /\ q \in ack[p]
                  /\ ~ Contains(pq,"req") /\ ~ Contains(qp,"ack") /\ ~ Contains(pq,"rel")
               \/ /\ q \notin ack[p] /\ Contains(qp,"ack")
                  /\ ~ Contains(pq,"req") /\ ~ Contains(pq,"rel")
               \/ /\ q \notin ack[p] /\ Contains(pq,"req")
                  /\ ~ Contains(qp,"ack") /\ Precedes(pq,"rel","req")

BasicInv == 
  /\ \A p,q \in Proc : NetworkInv(p,q)
  /\ \A p \in Proc : CommInv(p)

THEOREM BasicInvariant == Spec => []BasicInv
<1>1. Init => BasicInv
  BY DEF Init, BasicInv, CommInv, NetworkInv, Contains, AtMostOne
<1>2. TypeOK /\ BasicInv /\ [Next]_vars => BasicInv'
  <2> SUFFICES ASSUME TypeOK, BasicInv, [Next]_vars
               PROVE  BasicInv'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. ASSUME NEW n \in Proc, Request(n)
        PROVE  BasicInv'
    <3>1. /\ req[n][n] = 0
          /\ req' = [req EXCEPT ![n][n] = clock[n]]
          /\ network' = [network EXCEPT ![n] = Broadcast(n, ReqMessage(clock[n]))]
          /\ ack' =  [ack EXCEPT ![n] = {n}]
          /\ crit' = crit
      BY <2>1 DEF Request
    <3>. /\ ReqMessage(clock[n]) \in Message
         /\ ReqMessage(clock[n]).type = "req"
      BY DEF ReqMessage, Message
    <3>a. ~ (req[n][n] > 0)
      BY <3>1
    <3>2. /\ n \notin crit
          /\ \A q \in Proc : ~ Contains(network[n][q], "req") /\ ~ Contains(network[q][n], "ack")
      BY <3>a DEF BasicInv, CommInv
    <3>3. ASSUME NEW p \in Proc, NEW q \in Proc
          PROVE  NetworkInv(p,q)'
      BY <3>1, <3>2, <3>3, NotContainsSend, AtMostOneSend DEF Broadcast, BasicInv, NetworkInv
    <3>4. ASSUME NEW p \in Proc
          PROVE  CommInv(p)'
      <4>1. CASE p = n
        <5>. /\ req'[p][p] > 0 /\ p \in ack'[p]
             /\ p \notin crit'
          BY <3>1, <3>2, <4>1
        <5>. /\ ~ Contains(network'[p][n], "req")
             /\ ~ Contains(network'[n][p], "ack")
             /\ ~ Contains(network'[p][n], "rel")
          BY <3>3, <4>1 DEF NetworkInv, Contains
        <5>. ASSUME NEW q \in Proc \ {n}
             PROVE  /\ q \notin ack'[p]
                    /\ Contains(network'[p][q], "req")
                    /\ ~ Contains(network'[q][p], "ack")
          BY <3>1, <3>2, <4>1, ContainsSend DEF Broadcast
        <5>. \A q \in Proc \ {n} : Precedes(network[p][q], "rel", "req")
          BY <3>2, <4>1, NotContainsPrecedes
        <5>. \A q \in Proc \ {n} : Precedes(network'[p][q], "rel", "req")
          BY <3>1, <4>1, PrecedesSend DEF Broadcast
        <5>. QED  BY DEF CommInv
      <4>2. CASE p # n
        <5>. CommInv(p)
          BY DEF BasicInv
        <5>. UNCHANGED << req[p][p], ack[p], crit >>
          BY <3>1, <4>2
        <5>. \A q \in Proc : UNCHANGED network[p][q]
          BY <3>1, <4>2
        <5>. /\ \A q \in Proc \ {n} : UNCHANGED network[q][p]
             /\ p = n => UNCHANGED network[n][p]
          BY <3>1, <4>2 DEF Broadcast
        <5>. n # p => Contains(network'[n][p], "ack") <=> Contains(network[n][p], "ack")
          BY <3>1, <4>2, ContainsSend DEF Broadcast
        <5>. QED  BY DEF CommInv
      <4>. QED  BY <4>1, <4>2
    <3>. QED  BY <3>3, <3>4 DEF BasicInv
  <2>2. ASSUME NEW n \in Proc, Enter(n)
        PROVE  BasicInv'
    BY <2>2 DEF Enter, BasicInv, NetworkInv, CommInv
  <2>3. ASSUME NEW n \in Proc, Exit(n)
        PROVE  BasicInv'
    <3>1. /\ req[n][n] > 0
          /\ ack[n] = Proc
          /\ \A q \in Proc : /\ ~ Contains(network[n][q], "req")
                             /\ ~ Contains(network[q][n], "ack")
                             /\ ~ Contains(network[n][q], "rel")
          /\ network' = [network EXCEPT ![n] =
                          [q \in Proc |-> IF n=q THEN network[n][q] ELSE Append(network[n][q], RelMessage)]]
          /\ crit' = crit \ {n}
          /\ req' = [req EXCEPT ![n][n] = 0]
          /\ ack' = [ack EXCEPT ![n] = {}]
          /\ clock' = clock
      BY <2>3 DEF Exit, Broadcast, BasicInv, CommInv
    <3>. /\ RelMessage \in Message
         /\ RelMessage.type = "rel"
      BY DEF RelMessage, Message
    <3>2. ASSUME NEW p \in Proc, NEW q \in Proc
          PROVE  NetworkInv(p,q)'
      <4>1. CASE p = n
        <5>. /\ AtMostOne(network'[p][q], "req")
             /\ AtMostOne(network'[p][q], "rel")
          BY <3>1, <4>1, NotContainsAtMostOne, NotContainsSend
        <5>. AtMostOne(network[p][q], "ack")
          BY DEF BasicInv, NetworkInv
        <5>. AtMostOne(network'[p][q], "ack")
          BY <3>1, <4>1, AtMostOneSend
        <5>. network'[p][p] = << >>
          BY <3>1, <4>1 DEF BasicInv, NetworkInv
        <5>. QED  BY DEF NetworkInv
      <4>2. CASE p # n
        <5>. /\ network'[p][p] = network[p][p]
             /\ network'[p][q] = network[p][q]
          BY <3>1, <4>2
        <5>. QED  BY DEF BasicInv, NetworkInv
      <4>. QED  BY <4>1, <4>2
    <3>3. ASSUME NEW p \in Proc
          PROVE  CommInv(p)'
      <4>1. CASE p = n
        BY <3>1, <4>1, NotContainsSend DEF CommInv
      <4>2. CASE p # n
        <5>. /\ req'[p][p] = req[p][p]
             /\ ack'[p] = ack[p]
             /\ (p \in crit') <=> (p \in crit)
             /\ \A q \in Proc : network'[p][q] = network[p][q]
          BY <3>1, <4>2
        <5>. ASSUME NEW q \in Proc
             PROVE  Contains(network'[q][p], "ack") <=> Contains(network[q][p], "ack")
          <6>1. CASE n = q
            <7>. network'[q][p] = Append(network[q][p], RelMessage)
              BY  <3>1, <4>2, <6>1
            <7>. QED  BY ContainsSend
          <6>2. CASE n # q
            BY <3>1, <6>2
          <6>. QED  BY <6>1, <6>2
        <5>. QED  BY DEF BasicInv, CommInv
      <4>. QED  BY <4>1, <4>2
    <3>. QED  BY <3>2, <3>3 DEF BasicInv
  <2>4. ASSUME NEW n \in Proc, NEW k \in Proc \ {n}, ReceiveRequest(n,k)
        PROVE  BasicInv'
    <3>1. /\ network[k][n] # << >>
          /\ LET m == Head(network[k][n])
             IN  /\ m.type = "req"
                 /\ \A p \in Proc : req'[p][p] = req[p][p]
                 /\ network' = [network EXCEPT ![k][n] = Tail(network[k][n]),
                                               ![n][k] = Append(network[n][k], AckMessage)]
                 /\ UNCHANGED <<ack, crit>>
      BY <2>4 DEF ReceiveRequest
    <3>2. Contains(network[k][n], "req")
      BY <3>1 DEF Contains
    <3>3. /\ req[k][k] > 0 /\ k \in ack[k]
          /\ k \in crit => ack[k] = Proc
          /\ n \notin ack[k]
          /\ ~ Contains(network[n][k], "ack") /\ ~ Contains(network[k][n], "rel")
      BY <3>1, <3>2, PrecedesHead DEF BasicInv, CommInv
    <3>. /\ AckMessage \in Message
         /\ AckMessage.type = "ack"
      BY DEF AckMessage, Message
    <3>4. ASSUME NEW p \in Proc, NEW q \in Proc
          PROVE  NetworkInv(p,q)'
      <4>1. AtMostOne(network'[p][q], "req")
        BY <3>1, AtMostOneTail, AtMostOneSend, Zenon DEF BasicInv, NetworkInv
      <4>2. AtMostOne(network'[p][q], "ack")
        <5>. DEFINE nw == [network EXCEPT ![k][n] = Tail(network[k][n])]
        <5>1. /\ nw \in [Proc -> [Proc -> Seq(Message)]]
              /\ AtMostOne(nw[p][q], "ack")
              /\ ~ Contains(nw[n][k], "ack")
          BY <3>1, <3>3, AtMostOneTail DEF BasicInv, NetworkInv
        <5>. HIDE DEF nw
        <5>. DEFINE nw2 == [nw EXCEPT ![n][k] = Append(network[n][k], AckMessage)]
        <5>5. AtMostOne(nw2[p][q], "ack")
          BY <3>3, <5>1, NotContainsSend
        <5>. QED  BY <3>1, <5>5 DEF nw
      <4>3. AtMostOne(network'[p][q], "rel")
        BY <3>1, AtMostOneTail, AtMostOneSend, Zenon DEF BasicInv, NetworkInv
      <4>4. network'[p][p] = << >>
        BY <3>1 DEF BasicInv, NetworkInv
      <4>. QED  BY <4>1, <4>2, <4>3, <4>4 DEF NetworkInv
    <3>5. ASSUME NEW p \in Proc
          PROVE  CommInv(p)'
      <4>1. CASE p = k
        <5>. SUFFICES ASSUME NEW q \in Proc
                      PROVE  CommInv(p)!2!3!(q)'
          BY <3>1, <3>3, <4>1 DEF CommInv
        <5>. DEFINE pq == network[p][q]
                    qp == network[q][p]
        <5>1. CASE q = n
          <6>. q \notin ack'[p]
            BY <3>1, <3>3, <4>1, <5>1
          <6>. /\ pq # << >> /\ pq' = Tail(pq)
               /\ qp' = Append(qp, AckMessage)
               /\ AtMostOne(pq, "req") /\ Head(pq).type = "req"
               /\ ~ Contains(pq, "rel")
            BY <3>1, <3>3, <4>1, <5>1 DEF BasicInv, NetworkInv
          <6>. /\ Contains(qp', "ack")
               /\ ~ Contains(pq', "req")
               /\ ~ Contains(pq', "rel")
            BY ContainsSend, AtMostOneHead, ContainsTail DEF BasicInv, NetworkInv
          <6>. QED  OBVIOUS
        <5>2. CASE q # n
          <6>. pq' = pq /\ qp' = qp /\ ack'[p] = ack[p]
            BY <3>1, <3>3, <4>1, <5>2
          <6>. CommInv(p)!2!3!(q)
            BY <3>3, <4>1 DEF BasicInv, CommInv
          <6>. QED  OBVIOUS
        <5>. QED  BY <5>1, <5>2
      <4>2. CASE p = n
        <5>. UNCHANGED << req[p][p], ack[p], crit >>  BY <3>1
        <5>. ASSUME NEW q \in Proc
             PROVE  /\ Contains(network'[p][q], "req") <=> Contains(network[p][q], "req")
                    /\ Contains(network'[p][q], "rel") <=> Contains(network[p][q], "rel")
                    /\ Contains(network'[q][p], "ack") <=> Contains(network[q][p], "ack")
                    /\ Precedes(network'[p][q], "rel", "req") <=> Precedes(network[p][q], "rel", "req")
          <6>1. CASE q = k
            <7>. /\ network'[p][q] = Append(network[p][q], AckMessage)
                 /\ network[q][p] # << >> /\ Head(network[q][p]).type = "req"
                 /\ network'[q][p] = Tail(network[q][p])
              BY <3>1, <4>2, <6>1
            <7>. QED  BY ContainsSend, ContainsTail, PrecedesSend DEF BasicInv, NetworkInv
          <6>2. CASE q # k
            BY <3>1, <4>2, <6>2
          <6>. QED  BY <6>1, <6>2
        <5>. QED  BY DEF BasicInv, CommInv
      <4>3. CASE p \notin {k,n}  \* all relevant variables are unchanged
        <5>. \A q \in Proc : UNCHANGED <<req[p][p], ack, crit, network[p][q], network[q][p]>>
          BY <3>1, <4>3
        <5>. QED  BY DEF BasicInv, CommInv
      <4>. QED  BY <4>1, <4>2, <4>3
    <3>. QED  BY <3>4, <3>5 DEF BasicInv
  <2>5. ASSUME NEW n \in Proc, NEW k \in Proc \ {n}, ReceiveAck(n,k)
        PROVE  BasicInv'
    <3>1. /\ network[k][n] # << >>
          /\ Head(network[k][n]).type = "ack"
          /\ ack' = [ack EXCEPT ![n] = @ \union {k}]
          /\ network' = [network EXCEPT ![k][n] = Tail(@)]
          /\ UNCHANGED <<req, crit>>
      BY <2>5 DEF ReceiveAck
    <3>2. Contains(network[k][n], "ack")
      BY <3>1 DEF Contains
    <3>3. /\ req[n][n] > 0 /\ n \in ack[n]
          /\ n \in crit => ack[n] = Proc
          /\ k \notin ack[n]
          /\ ~ Contains(network[n][k], "req") /\ ~ Contains(network[n][k], "rel")
      BY <3>2 DEF BasicInv, CommInv
    <3>4. ASSUME NEW p \in Proc, NEW q \in Proc
          PROVE  NetworkInv(p,q)'
      BY <3>1, AtMostOneTail DEF BasicInv, NetworkInv
    <3>5. ASSUME NEW p \in Proc
          PROVE  CommInv(p)'
      <4>1. CASE p = n
        <5>. SUFFICES ASSUME NEW q \in Proc, CommInv(p)!2!3!(q)
                      PROVE  CommInv(p)!2!3!(q)'
          BY <3>1, <3>3, <4>1, ~(req[n][n] = 0) DEF BasicInv, CommInv
        <5>1. CASE q = k
          <6>. /\ q \in ack'[p]
               /\ ~ Contains(network'[p][q], "req")
               /\ ~ Contains(network'[p][q], "rel")
            BY <3>1, <3>3, <4>1, <5>1 DEF BasicInv, NetworkInv
          <6>. ~ Contains(network'[q][p], "ack")
            BY <3>1, <4>1, <5>1, AtMostOneHead, Zenon DEF BasicInv, NetworkInv
          <6>. QED  OBVIOUS
        <5>2. CASE q # k
          BY <3>1, <3>3, <4>1, <5>2
        <5>. QED  BY <5>1, <5>2
      <4>2. CASE p = k
        <5>. ASSUME NEW q \in Proc
             PROVE  /\ Contains(network'[p][q], "req") <=> Contains(network[p][q], "req")
                    /\ Contains(network'[p][q], "rel") <=> Contains(network[p][q], "rel")
                    /\ Precedes(network[p][q], "rel", "req") => Precedes(network'[p][q], "rel", "req")
          BY <3>1, <4>2, ContainsTail, PrecedesTail DEF BasicInv, NetworkInv
        <5>. QED  BY <3>1, <4>2 DEF BasicInv, CommInv
      <4>3. CASE p \notin {n,k}
        BY <3>1, <4>3 DEF BasicInv, CommInv
      <4>. QED  BY <4>1, <4>2, <4>3
    <3>. QED  BY <3>4, <3>5 DEF BasicInv
  <2>6. ASSUME NEW n \in Proc, NEW k \in Proc \ {n}, ReceiveRelease(n,k)
        PROVE  BasicInv'
    <3>1. /\ network[k][n] # << >>
          /\ Head(network[k][n]).type = "rel"
          /\ req' = [req EXCEPT ![n][k] = 0]
          /\ network' = [network EXCEPT ![k][n] = Tail(@)]
          /\ UNCHANGED <<ack, crit>>
      BY <2>6 DEF ReceiveRelease
    <3>2. ASSUME NEW p \in Proc, NEW q \in Proc
          PROVE  NetworkInv(p,q)'
      BY <3>1, AtMostOneTail DEF BasicInv, NetworkInv
    <3>3. ASSUME NEW p \in Proc, CommInv(p)
          PROVE  CommInv(p)'
      <4>. ASSUME NEW q \in Proc
           PROVE  /\ Contains(network'[p][q], "req") <=> Contains(network[p][q], "req")
                  /\ Contains(network'[q][p], "ack") <=> Contains(network[q][p], "ack")
                  /\ Precedes(network[p][q], "rel", "req") => Precedes(network'[p][q], "rel", "req")
        BY <3>1, ContainsTail, PrecedesTail DEF BasicInv, NetworkInv
      <4>. Contains(network[k][n], "rel")
        BY <3>1 DEF Contains
      <4>. ASSUME NEW q \in Proc, p # k \/ q # n
           PROVE  Contains(network'[p][q], "rel") <=> Contains(network[p][q], "rel")
        BY <3>1
      <4>. QED  BY <3>1, <3>3 DEF CommInv
    <3>. QED  BY <3>2, <3>3 DEF BasicInv
  <2>7. CASE UNCHANGED vars
    BY <2>7 DEF vars, BasicInv, CommInv, NetworkInv
  <2>8. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
<1>. QED  BY TypeCorrect, <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* The second invariant relates the clock values stored in the clock and   *)
(* req variables, as well as in request messages. Its proof relies on the  *)
(* "basic" invariant proved previously.                                    *)
(***************************************************************************)

ClockInvInner(p,q) ==
  LET pq == network[p][q]
      qp == network[q][p]
  IN  /\ \A i \in 1 .. Len(pq) : pq[i].type = "req" => pq[i].clock = req[p][p]
      /\ Contains(qp, "ack") \/ q \in ack[p] => 
             /\ req[q][p] = req[p][p]
             /\ clock[q] > req[p][p]
             /\ Precedes(qp, "ack", "req") =>
                  \A i \in 1 .. Len(qp) : qp[i].type = "req" => qp[i].clock > req[p][p]
      /\ p \in crit => beats(p,q)

ClockInv == \A p \in Proc : \A q \in Proc \ {p} : ClockInvInner(p,q)

THEOREM ClockInvariant == Spec => []ClockInv
<1>1. Init => ClockInv
  BY DEF Init, ClockInv, ClockInvInner, Contains
<1>2. TypeOK /\ BasicInv /\ ClockInv /\ [Next]_vars => ClockInv'
  <2> SUFFICES ASSUME TypeOK, BasicInv, ClockInv, [Next]_vars
               PROVE  ClockInv'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. ASSUME NEW n \in Proc, Request(n)
        PROVE  ClockInv'
    <3>1. /\ req[n][n] = 0
          /\ req' = [req EXCEPT ![n][n] = clock[n]]
          /\ network' = [network EXCEPT ![n] = Broadcast(n, ReqMessage(clock[n]))]
          /\ ack' =  [ack EXCEPT ![n] = {n}]
          /\ UNCHANGED <<clock, crit>>
          /\ n \notin crit
          /\ \A q \in Proc : ~ Contains(network[n][q], "req") /\ ~ Contains(network[q][n], "ack")
      BY <2>1 DEF Request, BasicInv, CommInv
    <3>. /\ ReqMessage(clock[n]) \in Message
         /\ ReqMessage(clock[n]).type = "req"
         /\ ReqMessage(clock[n]).clock = req'[n][n]
      BY <3>1 DEF ReqMessage, Message
    <3>2. ASSUME NEW p \in Proc, NEW q \in Proc \ {p}
          PROVE  ClockInvInner(p,q)'
      <4>1. CASE p = n
        <5>1. ASSUME NEW i \in 1 .. Len(network'[p][q]), network'[p][q][i].type = "req"
              PROVE  network'[p][q][i].clock = req'[p][p]
          BY <3>1, <4>1, <5>1 DEF Broadcast, Contains
        <5>2. ~ Contains(network'[q][p], "ack") /\ q \notin ack'[p]
          BY <3>1, <4>1 DEF Broadcast
        <5>3. p \notin crit'
          BY <3>1, <4>1
        <5>. QED  BY <5>1, <5>2, <5>3 DEF ClockInvInner
      <4>2. CASE q = n
        <5>1. ClockInvInner(p,q)
          BY DEF ClockInv
        <5>2. UNCHANGED << network[p][q], req[p][p], req[p][q], req[q][p], ack[p], crit >>
          BY <3>1, <4>2
        <5>. DEFINE qp == network[q][p]
        <5>3. ASSUME Contains(qp', "ack") \/ q \in ack'[p]
              PROVE  /\ req'[q][p] = req[p][p]
                     /\ clock'[q] > req'[p][p]
                     /\ Precedes(qp', "ack", "req") =>
                           \A i \in 1 .. Len(qp') : qp'[i].type = "req" => qp'[i].clock > req'[p][p]
          <6>. Contains(qp, "ack") \/ q \in ack[p]
            BY <3>1, <4>2, <5>3, ContainsSend DEF Broadcast
          <6>. QED
            BY <3>1, <4>2, <5>1 DEF ClockInvInner, Broadcast, Contains
        <5>. QED  BY <5>1, <5>2, <5>3 DEF ClockInvInner, beats
      <4>3. CASE n \notin {p,q}  \* all relevant variables unchanged
        BY <3>1, <4>3 DEF ClockInv, ClockInvInner, beats
      <4>. QED  BY <4>1, <4>2, <4>3
    <3>. QED  BY <3>2 DEF ClockInv
  <2>2. ASSUME NEW n \in Proc, Enter(n)
        PROVE  ClockInv'
    <3>. SUFFICES ASSUME NEW p \in Proc, NEW q \in Proc \ {p} 
                  PROVE ClockInvInner(p,q)'
      BY DEF ClockInv
    <3>1. CASE p = n
      BY <2>2, <3>1 DEF Enter, ClockInv, ClockInvInner, beats
    <3>2. CASE p # n
      BY <2>2, <3>2 DEF Enter, ClockInv, ClockInvInner, beats
    <3>. QED  BY <3>1, <3>2
  <2>3. ASSUME NEW n \in Proc, Exit(n)
        PROVE  ClockInv'
    <3>1. /\ n \in crit
          /\ crit' = crit \ {n}
          /\ network' = [network EXCEPT ![n] = Broadcast(n, RelMessage)]
          /\ req' = [req EXCEPT ![n][n] = 0]
          /\ ack' = [ack EXCEPT ![n] = {}]
          /\ clock' = clock
          /\ \A q \in Proc : /\ ~ Contains(network[n][q], "req")
                             /\ ~ Contains(network[q][n], "ack")
      BY <2>3 DEF Exit, BasicInv, CommInv
    <3>. RelMessage \in Message /\ RelMessage.type = "rel"
      BY DEF RelMessage, Message
    <3>2. ASSUME NEW p \in Proc, NEW q \in Proc \ {p}
          PROVE  ClockInvInner(p,q)'
      <4>1. CASE n = p
        BY <3>1, <4>1 DEF Broadcast, ClockInvInner, Contains
      <4>2. CASE n # p
        <5>1. /\ UNCHANGED << network[p][q], req[p][p], req[q][p], req[p][q], ack[p], clock >>
              /\ p \in crit' <=> p \in crit
          BY <3>1, <4>2
        <5>2. n # q => network'[q][p] = network[q][p]
          BY <3>1 DEF Broadcast
        <5>3. /\ Contains(network'[n][p], "ack") <=> Contains(network[n][p], "ack")
              /\ Precedes(network'[n][p], "ack", "req") <=> Precedes(network[n][p], "ack", "req")
          BY <3>1, <4>2, ContainsSend, PrecedesSend DEF Broadcast
        <5>4. \A i \in 1 .. Len(network'[n][p]) : network'[n][p][i].type # "req"
          BY <3>1 DEF Broadcast, Contains
        <5>. QED  BY <5>1, <5>2, <5>3, <5>4 DEF ClockInv, ClockInvInner, beats
      <4>. QED  BY <4>1, <4>2
    <3>. QED  BY <3>2 DEF ClockInv
  <2>4. ASSUME NEW n \in Proc, NEW k \in Proc \ {n}, ReceiveRequest(n,k)
        PROVE  ClockInv'
    <3>. DEFINE m == Head(network[k][n])
    <3>1. /\ network[k][n] # << >>
          /\ m.type = "req"
          /\ req' = [req EXCEPT ![n][k] = m.clock]
          /\ clock' = [clock EXCEPT ![n] = IF m.clock > clock[n] THEN m.clock + 1 
                                                                 ELSE clock[n]+1]
          /\ network' = [network EXCEPT ![k][n] = Tail(@),
                                        ![n][k] = Append(@, AckMessage)]
          /\ UNCHANGED <<ack, crit>>
          /\ Contains(network[k][n], "req")
      BY <2>4 DEF ReceiveRequest, ClockInv, ClockInvInner, Contains
    <3>2. m.clock = req[k][k]
      BY <3>1 DEF ClockInv, ClockInvInner, Contains
    <3>3. /\ req[k][k] > 0
          /\ n \notin ack[k] /\ k \notin crit
      BY <3>1 DEF BasicInv, CommInv
    <3>. AckMessage \in Message /\ AckMessage.type = "ack"
      BY DEF AckMessage, Message
    <3>4. ASSUME NEW p \in Proc, NEW q \in Proc \ {p}
          PROVE  ClockInvInner(p,q)'
      <4>. DEFINE pq == network[p][q]
                  qp == network[q][p]
      <4>. /\ ClockInvInner(p,q)
           /\ UNCHANGED req[p][p]
        BY <3>1 DEF ClockInv
      <4>1. CASE p = k /\ q = n
        <5>1. pq' = Tail(pq)
          BY <3>1, <4>1, Zenon
        <5>2. ~ Contains(pq', "req")
          BY <3>1, <4>1, <5>1, ContainsTail DEF BasicInv, NetworkInv
        <5>3. clock'[q] > req'[p][p]
          BY <3>1, <3>2, <3>3, <4>1
        <5>4. /\ req'[q][p] = req'[p][p]
              /\ q \notin ack'[p]
              /\ p \notin crit'
          BY <3>1, <3>2, <3>3, <4>1
        <5>5. ASSUME Precedes(qp', "ack", "req"), 
                     NEW i \in 1 .. Len(qp'), qp'[i].type = "req"
              PROVE  FALSE
          BY <3>1, <4>1, <5>5 DEF Precedes
        <5>. QED  BY <5>2, <5>3, <5>4, <5>5 DEF ClockInvInner, Contains
      <4>2. CASE p = k /\ q # n
        BY <3>1, <4>2 DEF ClockInvInner, beats
      <4>3. CASE p = n /\ q = k
        <5>1. UNCHANGED << req[q][p], clock[q], ack >>
          BY <3>1, <4>3
        <5>2. ASSUME NEW i \in 1 .. Len(pq'), pq'[i].type = "req"
              PROVE  i \in 1 .. Len(pq) /\ pq'[i] = pq[i]
          BY <3>1, <4>3, <5>2
        <5>3. qp' = Tail(qp) /\ Head(qp).type = "req" /\ qp # << >>
          BY <3>1, <4>3, Zenon
        <5>4. Contains(qp', "ack") <=> Contains(qp, "ack")
          BY <5>3, ContainsTail DEF BasicInv, NetworkInv
        <5>5. ~ Contains(qp', "req")
          BY <5>3, ContainsTail DEF BasicInv, NetworkInv
        <5>7. ASSUME p \in crit'
              PROVE  beats(p,q)'
          <6>. /\ p \in crit
               /\ q \in ack[p]
               /\ ~ Contains(qp, "ack")
            BY <3>1, <4>3, <5>7 DEF BasicInv, CommInv
          <6>. Precedes(qp, "ack", "req")
            BY NotContainsPrecedes
          <6>. req'[p][q] > req[p][p]
            BY <3>1, <4>3, m = qp[1], 1 \in 1 .. Len(qp) DEF ClockInvInner
          <6>. QED  BY DEF beats
        <5>. QED  BY <5>1, <5>2, <5>4, <5>5, <5>7, Zenon DEF ClockInvInner, Contains
      <4>4. CASE p = n /\ q # k
        BY <3>1, <4>4 DEF ClockInvInner, beats
      <4>5. CASE  p \notin {n,k} /\ q = n
        <5>. UNCHANGED <<pq, qp, req[p][q], req[q][p], ack, crit>>
          BY <3>1, <4>5
        <5>. clock[q] > req[p][p] => clock'[q] > req[p][p]
          BY <3>1, <3>2, <4>5
        <5>. QED  BY DEF ClockInvInner, beats
      <4>6. CASE p \notin {n,k} /\ q # n
        BY <3>1, <4>6, Zenon DEF ClockInvInner, beats
      <4>. QED  BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6
    <3>. QED  BY <3>4 DEF ClockInv
  <2>5. ASSUME NEW n \in Proc, NEW k \in Proc \ {n}, ReceiveAck(n,k)
        PROVE  ClockInv'
    <3>1. /\ network[k][n] # << >>
          /\ Head(network[k][n]).type = "ack"
          /\ ack' = [ack EXCEPT ![n] = @ \union {k}]
          /\ network' = [network EXCEPT ![k][n] = Tail(@)]
          /\ UNCHANGED <<clock, req, crit>>
          /\ Contains(network[k][n], "ack")
      BY <2>5 DEF ReceiveAck, BasicInv, CommInv, Contains
    <3>2. ASSUME NEW p \in Proc , NEW q \in Proc \ {p}, ClockInvInner(p,q)
          PROVE  ClockInvInner(p,q)'
      <4>. DEFINE pq == network[p][q]
                  qp == network[q][p]
      <4>1. CASE p = n /\ q = k
        <5>1. /\ qp # << >>
              /\ Head(qp).type = "ack"
              /\ Contains(qp, "ack")
              /\ qp' = Tail(qp)
              /\ UNCHANGED << pq, clock, req, crit >>
          BY <3>1, <4>1
        <5>2. ASSUME Precedes(qp', "ack", "req")
              PROVE  Precedes(qp, "ack", "req")
          BY <5>1, <5>2, PrecedesInTail, Zenon
        <5>3. ASSUME NEW i \in 1 .. Len(qp'), qp'[i].type = "req"
              PROVE  i+1 \in 1 .. Len(qp) /\ qp'[i] = qp[i+1]
          BY <5>1
        <5>. QED  BY <3>2, <5>1, <5>2, <5>3 DEF ClockInvInner, beats
      <4>2. CASE p = k /\ q = n
        <5>1. UNCHANGED << qp, ack[p], clock, req, crit >>
          BY <3>1, <4>2
        <5>2. ASSUME NEW i \in 1 .. Len(pq')
              PROVE  i+1 \in 1 .. Len(pq) /\ pq'[i] = pq[i+1]
          BY <3>1, <4>2
        <5>. QED  BY <3>2, <5>1, <5>2 DEF ClockInvInner, beats
      <4>3. CASE {p,q} # {n,k}
        BY <3>1, <3>2, <4>3 DEF ClockInvInner, beats
      <4>. QED  BY <4>1, <4>2, <4>3, Zenon
    <3>. QED  BY <3>2 DEF ClockInv
  <2>6. ASSUME NEW n \in Proc, NEW k \in Proc \ {n}, ReceiveRelease(n,k)
        PROVE  ClockInv'
    <3>1. /\ network[k][n] # << >>
          /\ Head(network[k][n]).type = "rel"
          /\ req' = [req EXCEPT ![n][k] = 0]
          /\ network' = [network EXCEPT ![k][n] = Tail(@)]
          /\ UNCHANGED << clock, ack, crit >>
          /\ Contains(network[k][n], "rel")
      BY <2>6 DEF ReceiveRelease, Contains\*, BasicInv, CommInv, Contains
    <3>2. /\ ~ Contains(network[n][k], "ack")
          /\ n \notin ack[k]
      BY <3>1, Zenon DEF BasicInv, CommInv
    <3>3. ASSUME NEW p \in Proc, NEW q \in Proc, ClockInvInner(p,q)
          PROVE  ClockInvInner(p,q)'
      <4>. DEFINE pq == network[p][q]
                  qp == network[q][p]
      <4>1. CASE p = n /\ q = k
        <5>. /\ UNCHANGED << pq, ack, req[p][p], req[q][p], clock >>
             /\ beats(p,q)'
             /\ \A i \in 1 .. Len(qp') : i+1 \in 1 .. Len(qp) /\ qp'[i] = qp[i+1]
          BY <3>1, <4>1 DEF beats
        <5>. Contains(qp', "ack") <=> Contains(qp, "ack")
          BY <3>1, <4>1, ContainsTail DEF BasicInv, NetworkInv
        <5>. Precedes(qp', "ack", "req") => Precedes(qp, "ack", "req")
          BY <3>1, <4>1, PrecedesInTail, Zenon
        <5>. QED  BY <3>3, Zenon DEF ClockInvInner
      <4>2. CASE p = k /\ q = n
        <5>. /\ UNCHANGED << qp, ack, req[p][p], req[p][q], crit, clock >>
             /\ ~ Contains(qp', "ack") /\ q \notin ack'[p]
             /\ \A i \in 1 .. Len(pq') : i+1 \in 1 .. Len(pq) /\ pq'[i] = pq[i+1]
          BY <3>1, <3>2, <4>2
        <5>. QED  BY <3>3 DEF ClockInvInner, beats
      <4>3. CASE {p,q} # {k,n}
        BY <3>1, <3>3, <4>3 DEF ClockInvInner, beats
      <4>. QED  BY <4>1, <4>2, <4>3, Zenon
    <3>. QED  BY <3>3 DEF ClockInv
  <2>7. CASE UNCHANGED vars
    BY <2>7 DEF ClockInv, ClockInvInner, beats, vars
  <2>8. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next
<1>. QED  BY <1>1, <1>2, TypeCorrect, BasicInvariant, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Mutual exclusion is a simple consequence of the above invariants.       *)
(* In particular, if two distinct processes p and q were ever in the       *)
(* critical section at the same instant, then beats(p,q) and beats(q,p)    *)
(* would both have to hold, but this is impossible.                        *)
(***************************************************************************)
THEOREM Safety == Spec => []Mutex
<1>1. TypeOK /\ BasicInv /\ ClockInv => Mutex
  <2>. SUFFICES ASSUME TypeOK, BasicInv, ClockInv,
                       NEW p \in crit, NEW q \in crit, p # q
                PROVE  FALSE
    BY DEF Mutex
  <2>. USE DEF TypeOK
  <2>. /\ req[p][p] > 0 /\ req[q][q] > 0
       /\ p \in ack[q] /\ q \in ack[p]
    BY DEF BasicInv, CommInv
  <2>. /\ req[q][p] = req[p][p]
       /\ req[p][q] = req[q][q]
       /\ beats(p,q)
       /\ beats(q,p)
    BY DEF ClockInv, ClockInvInner
  <2>. QED  BY NType DEF Proc, beats
<1>. QED  BY TypeCorrect, BasicInvariant, ClockInvariant, <1>1, PTL

==============================================================================
