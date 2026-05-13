------------------------------ MODULE IndInv_apa ------------------------------
(***************************************************************************)
(* Apalache-based search for an inductive strengthening of tcp.tla's Inv. *)
(*                                                                         *)
(*  *** SUCCESS ***                                                        *)
(*                                                                         *)
(*  After ~26 counterexample-driven iterations, the candidate IndInv      *)
(*  defined below is INDUCTIVE for the bounded model (MaxLen=4):          *)
(*                                                                         *)
(*    apalache-mc check --config=IndInv_apa_init.cfg --length=0           *)
(*        checks Init => IndInv  -->  EXITCODE: OK   (~5s)                *)
(*                                                                         *)
(*    apalache-mc check --config=IndInv_apa.cfg --length=1                *)
(*        checks IndInv /\ [Next]_vars => IndInv'  -->  EXITCODE: OK     *)
(*        (~70s)                                                          *)
(*                                                                         *)
(*  Since Inv is a conjunct of IndInv, the standard inductive argument   *)
(*  yields:                                                                *)
(*                                                                         *)
(*    Spec  =>  []IndInv  =>  []Inv                                        *)
(*                                                                         *)
(*  for executions in which every queue stays bounded by MaxLen=4.        *)
(*                                                                         *)
(* The final IndInv has 7 auxiliary clauses (in addition to TypeOK and    *)
(* Inv), each of which proved necessary to discharge a counterexample:    *)
(*                                                                         *)
(*   1. Aux_singleton_RST       (iter 1)                                  *)
(*      n[p]=<<RST>> /\ n[q]=<<>>  =>  connstate[q] /= EST                *)
(*      The original SynReceived(RST) trigger.                            *)
(*                                                                         *)
(*   2. Aux_singleton_ACK       (iter 2)                                  *)
(*      n[p]=<<ACK>> /\ n[q]=<<>> /\ connstate[p]=SR                      *)
(*           =>  connstate[q]=EST                                          *)
(*      The SynReceived(ACK) trigger.                                     *)
(*                                                                         *)
(*   3. Aux_singleton_ACKofFIN  (iter 3)                                  *)
(*      n[p]=<<ACKofFIN>> /\ n[q]=<<>> /\ connstate[p] in {FW1,CLOSING,LA}*)
(*           =>  connstate[q] /= EST                                       *)
(*      The FW1/Closing/LastAck triggers.                                 *)
(*                                                                         *)
(*   4. Aux_EST_evidence        (iter 22, 25, 26)                         *)
(*      connstate[p]=EST  =>  q in PostEst OR a TCP-message in either    *)
(*      queue (handshake or teardown) is present.                         *)
(*      Forbids "p reached EST with no trace anywhere".                   *)
(*                                                                         *)
(*   5. Aux_LastMsg             (iter 23)                                 *)
(*      For q in {SR, FW1, CW, LA, CLOSING, SS}, the last element of    *)
(*      n[p] equals the message q appended on entry to that state.       *)
(*      Captures "while q stays in X, no further appends from q".         *)
(*                                                                         *)
(*   6. Aux_RST_at_end          (iter 24)                                 *)
(*      LastMsg(p)=RST  =>  connstate[q] in {TIME-WAIT, CLOSED, LISTEN}.  *)
(*      Captures "after Note3 send q is in TW; q can transit only        *)
(*      through CLOSED/LISTEN without re-touching n[p]".                  *)
(*                                                                         *)
(* Iteration history (~26 iterations).  Several "structural" candidates   *)
(* I tried (Aux_RST_head, Aux_q_PostEst, Aux_FIN_handshake_predecessor   *)
(* with a "p in PostEst" disjunct, Aux_SR_q_EST_has_ACK) turned out to   *)
(* be OVER-RESTRICTIVE: they were violated by reachable post-states     *)
(* where Inv was vacuously true on a singleton.  The successful         *)
(* invariant is built from the singleton triggers + a careful evidence  *)
(* clause for EST + LastMsg per state + the Note3-RST anchor.           *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Apalache

CONSTANT
  \* @type: Set(PEER);
  Peers,
  \* @type: Int;
  MaxLen

VARIABLE
  \* @type: PEER -> Bool;
  tcb,
  \* @type: PEER -> Str;
  connstate,
  \* @type: PEER -> Seq(Str);
  network

INSTANCE tcp

PeersVal == { "p1_OF_PEER", "p2_OF_PEER" }
MaxLenVal == 4

Msgs == {"SYN", "SYN,ACK", "ACK", "RST", "FIN", "ACKofFIN"}

(***************************************************************************)
(* Apalache-friendly "havoc" for the inductive-invariant initial state.   *)
(***************************************************************************)
\* @type: () => PEER -> Bool;
GenTcb == [p \in Peers |-> Gen(1)]
\* @type: () => PEER -> Str;
GenConnstate == [p \in Peers |-> Gen(1)]
\* @type: () => PEER -> Seq(Str);
GenNetwork == [p \in Peers |-> Gen(MaxLen)]

(***************************************************************************)
(* Type-correctness clause that uses a constant index range so Apalache   *)
(* can enumerate.                                                         *)
(***************************************************************************)
TypeOKBounded ==
  /\ tcb \in [Peers -> BOOLEAN]
  /\ connstate \in [Peers -> States]
  /\ \A p \in Peers :
       \A i \in 1..MaxLen :
         (i <= Len(network[p])) => network[p][i] \in Msgs

BoundedNetwork ==
  \A p \in Peers : Len(network[p]) \in 0..MaxLen

(***************************************************************************)
(* Helper.                                                                  *)
(***************************************************************************)
HasMsg(m, p) ==
  \E i \in 1..MaxLen : i <= Len(network[p]) /\ network[p][i] = m

PostEstStrict == {"ESTABLISHED", "FIN-WAIT-1", "FIN-WAIT-2", "CLOSING",
                  "CLOSE-WAIT", "LAST-ACK", "TIME-WAIT"}
PostEst       == PostEstStrict \cup {"CLOSED"}

(***************************************************************************)
(* Singleton-form Aux invariants -- one for each "consume-only" action    *)
(* that can leave the system in the both-empty configuration.             *)
(***************************************************************************)
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

(***************************************************************************)
(* iter 22: if p is in ESTABLISHED, then either q is also in PostEst or   *)
(* there is handshake-completion evidence (ACK or SYN,ACK) in q's queue  *)
(* or teardown evidence in p's queue.                                    *)
(***************************************************************************)
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

(***************************************************************************)
(* iter 23: while q is in a state X whose entry transition appends a     *)
(* known message m to n[p], the LAST element of n[p] (if non-empty)      *)
(* equals m.  Apalache used n[p1]=<<"ACK">> with p2=SR -- but p2's last *)
(* append (Listen/SynSent SYN entering SR) writes SYN,ACK, not ACK.     *)
(* For SR, FW1, CW, LA, CLOSING the entry transition has a fixed        *)
(* append pattern; for the others (LISTEN, EST, FW2, TW, CLOSED, SS)   *)
(* the entry may be no-append, so we cannot constrain.                  *)
(***************************************************************************)
LastMsg(p) == network[p][Len(network[p])]

Aux_LastMsg ==
  \A p, q \in Peers :
    (p # q /\ network[p] # <<>>) =>
      /\ connstate[q] = "SYN-RECEIVED"  => LastMsg(p) = "SYN,ACK"
      /\ connstate[q] = "FIN-WAIT-1"    => LastMsg(p) \in {"FIN", "RST"}
      /\ connstate[q] = "CLOSE-WAIT"    => LastMsg(p) = "ACKofFIN"
      /\ connstate[q] = "LAST-ACK"      => LastMsg(p) = "FIN"
      /\ connstate[q] = "CLOSING"       => LastMsg(p) = "ACKofFIN"
      /\ connstate[q] = "SYN-SENT"      => LastMsg(p) = "SYN"

(***************************************************************************)
(* iter 24: when the LAST element of n[p] is RST, q just sent RST via    *)
(* Note3 and is therefore in {TIME-WAIT, CLOSED, LISTEN} (no further    *)
(* q-action could have appended to n[p] without changing its last       *)
(* element).                                                              *)
(***************************************************************************)
Aux_RST_at_end ==
  \A p, q \in Peers :
    (p # q /\ network[p] # <<>> /\ LastMsg(p) = "RST")
       => connstate[q] \in {"TIME-WAIT", "CLOSED", "LISTEN"}

(***************************************************************************)
(* Candidate inductive invariant (singleton-form only).                   *)
(***************************************************************************)
IndInv ==
  /\ TypeOKBounded
  /\ BoundedNetwork
  /\ Inv
  /\ Aux_singleton_RST
  /\ Aux_singleton_ACK
  /\ Aux_singleton_ACKofFIN
  /\ Aux_EST_evidence
  /\ Aux_LastMsg
  /\ Aux_RST_at_end

(***************************************************************************)
(* Symbolic-init form of IndInv.                                          *)
(***************************************************************************)
IndInit ==
  /\ tcb = GenTcb
  /\ connstate = GenConnstate
  /\ network = GenNetwork
  /\ IndInv

(***************************************************************************)
(* Bounded-step transition that keeps the queue length within MaxLen.    *)
(***************************************************************************)
NextBounded ==
  /\ Next
  /\ \A p \in Peers : Len(network'[p]) \in 0..MaxLen

==============================================================================
