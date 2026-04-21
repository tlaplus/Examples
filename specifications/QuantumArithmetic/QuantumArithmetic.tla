------------------------------ MODULE QuantumArithmetic ------------------------------
EXTENDS Naturals, Integers, TLC

(*
  QuantumArithmetic.tla — Quantum Arithmetic generator algebra.
  ------------------------------------------------------------------------

  This module specifies the state machine of the Quantum Arithmetic
  Reachability Module (QARM): a discrete system over pairs (b, e) with
  derived coordinates d = b + e, a = b + 2e (equivalently a = d + e), a
  duo-modular invariant qtag = 24*phi9(a) + phi24(a) \in [0, 239], and
  three generator actions:

    sigma  : e -> e + 1                            (e-growth)
    mu     : swap b <-> e                          (coordinate swap)
    lambda : (b, e) -> (k*b, k*e) for k in KSet    (scaling)

  Each generator is paired with explicit failure actions — OUT_OF_BOUNDS
  when the successor tuple would exceed CAP, FIXED_Q_VIOLATION when the
  successor would break duo-modular invariance. Failure states are
  absorbing: once fail /= "OK", the tuple is frozen.

  This file restricts Init to b, e \in 1..CAP (rather than 0..CAP), so
  QA Axiom A1 (No-Zero) holds structurally over the reachable state
  graph. See README.md and the sibling module QuantumArithmeticAxioms.tla
  for the full axiom set.

  Primary references:
    - Lamport, L. (1994). The Temporal Logic of Actions. ACM TOPLAS 16(3),
      872-923. DOI: 10.1145/177492.177726.
    - Lamport, L. (2002). Specifying Systems: The TLA+ Language and Tools
      for Hardware and Software Engineers. Addison-Wesley.
      ISBN 978-0-321-14306-8.

  TLC requirements:
    - CAP finite (e.g. 20..50)
    - KSet finite (e.g. {2, 3})

  See QuantumArithmetic.cfg for the standard bounded model.
*)

CONSTANTS
  CAP,          \* bound on b,e,d,a
  KSet          \* finite set of scaling factors for lambda (e.g. {2,3})

VARIABLES
  b, e, d, a,
  qtag,
  fail,         \* {"OK","OUT_OF_BOUNDS","FIXED_Q_VIOLATION","ILLEGAL"}
  lastMove      \* {"NONE","σ","μ","λ"}

(*** Helpers ***)

InCap(x) == x \in 0..CAP

DR(n) ==
  IF n = 0 THEN 0 ELSE 1 + ((n - 1) % 9)

Phi24(n) == n % 24
Phi9(n)  == DR(n)

QDef(bv, ev, dv, av) == 24 * Phi9(av) + Phi24(av)

TupleClosed(bv, ev, dv, av) ==
  /\ bv \in Nat /\ ev \in Nat /\ dv \in Nat /\ av \in Nat
  /\ dv = bv + ev
  /\ av = dv + ev

InBounds(bv, ev, dv, av) ==
  /\ InCap(bv) /\ InCap(ev) /\ InCap(dv) /\ InCap(av)

StateOK ==
  /\ TupleClosed(b, e, d, a)
  /\ InBounds(b, e, d, a)
  /\ qtag = QDef(b, e, d, a)
  /\ fail \in {"OK","OUT_OF_BOUNDS","FIXED_Q_VIOLATION","ILLEGAL"}
  /\ lastMove \in {"NONE","σ","μ","λ"}

(*** Init — A1-corrected: b, e \in 1..CAP (not 0..CAP) ***)

Init ==
  /\ b \in 1..CAP             \* A1: No-Zero.
  /\ e \in 1..CAP             \* A1: No-Zero.
  /\ d = b + e
  /\ a = d + e
  /\ TupleClosed(b, e, d, a)
  /\ InBounds(b, e, d, a)
  /\ qtag = QDef(b, e, d, a)
  /\ fail = "OK"
  /\ lastMove = "NONE"

(*** Move actions — generator algebra ***)

(*** σ : growth on e by +1; close tuple canonically ***)

SigmaSucc ==
  LET e2 == e + 1 IN
  LET b2 == b IN
  LET d2 == b2 + e2 IN
  LET a2 == d2 + e2 IN
  /\ fail = "OK"
  /\ InBounds(b2, e2, d2, a2)
  /\ QDef(b2, e2, d2, a2) = qtag
  /\ b' = b2 /\ e' = e2 /\ d' = d2 /\ a' = a2
  /\ qtag' = qtag
  /\ fail' = "OK"
  /\ lastMove' = "σ"

SigmaFail_OUT_OF_BOUNDS ==
  LET e2 == e + 1 IN
  LET b2 == b IN
  LET d2 == b2 + e2 IN
  LET a2 == d2 + e2 IN
  /\ fail = "OK"
  /\ ~InBounds(b2, e2, d2, a2)
  /\ UNCHANGED <<b,e,d,a,qtag>>
  /\ fail' = "OUT_OF_BOUNDS"
  /\ lastMove' = "σ"

SigmaFail_FIXED_Q ==
  LET e2 == e + 1 IN
  LET b2 == b IN
  LET d2 == b2 + e2 IN
  LET a2 == d2 + e2 IN
  /\ fail = "OK"
  /\ InBounds(b2, e2, d2, a2)
  /\ QDef(b2, e2, d2, a2) # qtag
  /\ UNCHANGED <<b,e,d,a,qtag>>
  /\ fail' = "FIXED_Q_VIOLATION"
  /\ lastMove' = "σ"

Sigma ==
  SigmaSucc \/ SigmaFail_OUT_OF_BOUNDS \/ SigmaFail_FIXED_Q


(*** μ : swap b <-> e; close tuple canonically ***)

MuSucc ==
  LET b2 == e IN
  LET e2 == b IN
  LET d2 == b2 + e2 IN
  LET a2 == d2 + e2 IN
  /\ fail = "OK"
  /\ InBounds(b2, e2, d2, a2)
  /\ QDef(b2, e2, d2, a2) = qtag
  /\ b' = b2 /\ e' = e2 /\ d' = d2 /\ a' = a2
  /\ qtag' = qtag
  /\ fail' = "OK"
  /\ lastMove' = "μ"

MuFail_OUT_OF_BOUNDS ==
  LET b2 == e IN
  LET e2 == b IN
  LET d2 == b2 + e2 IN
  LET a2 == d2 + e2 IN
  /\ fail = "OK"
  /\ ~InBounds(b2, e2, d2, a2)
  /\ UNCHANGED <<b,e,d,a,qtag>>
  /\ fail' = "OUT_OF_BOUNDS"
  /\ lastMove' = "μ"

MuFail_FIXED_Q ==
  LET b2 == e IN
  LET e2 == b IN
  LET d2 == b2 + e2 IN
  LET a2 == d2 + e2 IN
  /\ fail = "OK"
  /\ InBounds(b2, e2, d2, a2)
  /\ QDef(b2, e2, d2, a2) # qtag
  /\ UNCHANGED <<b,e,d,a,qtag>>
  /\ fail' = "FIXED_Q_VIOLATION"
  /\ lastMove' = "μ"

Mu ==
  MuSucc \/ MuFail_OUT_OF_BOUNDS \/ MuFail_FIXED_Q


(*** λ_k : scale (b,e) by k; close tuple canonically ***)

LambdaSucc ==
  \E k \in KSet :
    LET b2 == k * b IN
    LET e2 == k * e IN
    LET d2 == b2 + e2 IN
    LET a2 == d2 + e2 IN
    /\ fail = "OK"
    /\ InBounds(b2, e2, d2, a2)
    /\ QDef(b2, e2, d2, a2) = qtag
    /\ b' = b2 /\ e' = e2 /\ d' = d2 /\ a' = a2
    /\ qtag' = qtag
    /\ fail' = "OK"
    /\ lastMove' = "λ"

LambdaFail_OUT_OF_BOUNDS ==
  \E k \in KSet :
    LET b2 == k * b IN
    LET e2 == k * e IN
    LET d2 == b2 + e2 IN
    LET a2 == d2 + e2 IN
    /\ fail = "OK"
    /\ ~InBounds(b2, e2, d2, a2)
    /\ UNCHANGED <<b,e,d,a,qtag>>
    /\ fail' = "OUT_OF_BOUNDS"
    /\ lastMove' = "λ"

LambdaFail_FIXED_Q ==
  \E k \in KSet :
    LET b2 == k * b IN
    LET e2 == k * e IN
    LET d2 == b2 + e2 IN
    LET a2 == d2 + e2 IN
    /\ fail = "OK"
    /\ InBounds(b2, e2, d2, a2)
    /\ QDef(b2, e2, d2, a2) # qtag
    /\ UNCHANGED <<b,e,d,a,qtag>>
    /\ fail' = "FIXED_Q_VIOLATION"
    /\ lastMove' = "λ"

Lambda ==
  LambdaSucc \/ LambdaFail_OUT_OF_BOUNDS \/ LambdaFail_FIXED_Q


(*** Global Next ***************************************************************)

Next ==
  \/ Sigma
  \/ Mu
  \/ Lambda
  \/ /\ fail # "OK" /\ UNCHANGED <<b,e,d,a,qtag,fail,lastMove>>
     \* absorbing stutter once failure recorded (keeps failure states distinct)

Spec ==
  Init /\ [][Next]_<<b,e,d,a,qtag,fail,lastMove>>

(*** Invariants ****************************************************************)

Inv_TupleClosed == TupleClosed(b,e,d,a)
Inv_InBounds    == InBounds(b,e,d,a)
Inv_QDef        == qtag = QDef(b,e,d,a)
Inv_FailDomain  == fail \in {"OK","OUT_OF_BOUNDS","FIXED_Q_VIOLATION","ILLEGAL"}
Inv_MoveDomain  == lastMove \in {"NONE","σ","μ","λ"}

THEOREM Spec => []Inv_TupleClosed
THEOREM Spec => []Inv_InBounds
THEOREM Spec => []Inv_QDef
THEOREM Spec => []Inv_FailDomain
THEOREM Spec => []Inv_MoveDomain

===============================================================================
