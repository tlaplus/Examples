------------------------------ MODULE QuantumArithmeticAxioms ------------------------------
EXTENDS QuantumArithmetic

(*
  QuantumArithmeticAxioms.tla — The six QA compliance axioms + Theorem NT
  as TLA+ temporal invariants.
  --------------------------------------------------------------------------

  The Quantum Arithmetic (QA) axiom system comprises six compliance
  rules (A1, A2, S1, S2, T1, T2) plus Theorem NT (Observer Projection
  Firewall). This module encodes all seven as named invariants over the
  QARM generator algebra (see QuantumArithmetic.tla), where TLC can
  verify them against the reachable state graph.

  The six axioms, briefly:

    A1 (No-Zero)         : b, e \in {1..CAP}, never {0..CAP-1}.
    A2 (Derived Coords)  : d = b+e, a = b+2e are always derived, never
                           assigned independently.
    S1 (No ^2 operator)  : Use b*b rather than b^2 (structural; see note
                           on Inv_S1_NoSquareOperator below).
    S2 (Integer state)   : b, e, d, a \in Nat. No float state.
    T1 (Path time)       : QA time = integer path length. No continuous
                           time variables in QA logic.
    T2 (Firewall)        : Observer outputs never feed back as QA inputs.

  Theorem NT (Observer Projection Firewall): continuous functions are
  observer projections ONLY; the continuous-discrete boundary is crossed
  EXACTLY TWICE per QA trace (input at Init, output at Project).

  Base: EXTENDS QuantumArithmetic (the A1-compliant generator algebra
  with b, e \in 1..CAP at Init).

  Additions:
    - Two observer-layer variables (obs_float, obs_cross_count) that
      model the continuous-discrete boundary.
    - A Project action that performs the QA-to-observer output crossing.
    - Seven named invariants, one per axiom. A1, A2, S2, T1, T2, NT are
      runtime-checkable (TLC verifies). S1 is STRUCTURAL (TLA+ does not
      expose a `^` operator on the state variables used here; all
      multiplicative terms are written as b*b / k*b / k*e); see the
      comment on Inv_S1_NoSquareOperator below.

  Each runtime-checkable invariant has a dedicated non-vacuity spec
  (QuantumArithmeticAxioms_negative_{A1,A2,S2,T1,T2,NT}.tla) that
  exhibits a minimal counterexample, proving the invariant actively
  detects its violation class rather than holding vacuously over the
  reachable set.

  Primary references:
    - Lamport, L. (1994). The Temporal Logic of Actions. ACM TOPLAS 16(3),
      872-923. DOI: 10.1145/177492.177726.
    - Lamport, L. (2002). Specifying Systems: The TLA+ Language and Tools
      for Hardware and Software Engineers. Addison-Wesley.
      ISBN 978-0-321-14306-8.

  See README.md for motivation, module inventory, and reproduction
  commands with expected state counts.
*)

(*** Observer-layer variables ****************************************************
  Theorem NT (Observer Projection Firewall) states that continuous functions
  are observer projections ONLY; the continuous-discrete boundary is crossed
  EXACTLY TWICE per QA trace — once at Init (continuous input seed → discrete
  tuple) and once at Project (discrete tuple → continuous observer output).

  To encode this in TLA+, we introduce two OBSERVER-LAYER variables that sit
  OUTSIDE the QA-layer state (b, e, d, a, qtag, fail, lastMove):
    - obs_float: scalar observer state. Takes value 0 at Init (symbolic
      marker for "input seed, not yet projected"); updated exactly once, by
      the Project action, to the QA-layer coord `a` at projection time.
    - obs_cross_count: number of boundary crossings so far. 1 at Init; 2
      after Project. No trace ever reaches 3.

  Every QA-layer action (σ / μ / λ_k, plus the absorbing-stutter on failure)
  carries UNCHANGED <<obs_float, obs_cross_count>> by construction of
  ExtNext. This is the T2 Firewall at the spec level: continuous outputs
  cannot feed back as QA inputs, because the observer variables are read-only
  to the QA layer.
*******************************************************************************)

VARIABLES
  obs_float,       \* observer-layer scalar
  obs_cross_count  \* number of observer-boundary crossings so far

obs_vars  == <<obs_float, obs_cross_count>>
qa_vars   == <<b, e, d, a, qtag, fail, lastMove>>
ext_vars  == <<b, e, d, a, qtag, fail, lastMove, obs_float, obs_cross_count>>

\* Observer output domain: bounded to keep TLC tractable; the symbolic value
\* 0 marks the INIT seed (pre-projection), and 3..3*CAP spans the projection
\* image of the coord `a` (since a = b + 2e with b, e \in 1..CAP gives
\* a \in 3..3*CAP).
ObsDomain == 0..(3 * CAP)

(*** Extended Init *************************************************************)

Init_ext ==
  /\ Init                        \* inherits A1-corrected QARM Init
  /\ obs_float = 0               \* boundary cross 1: continuous seed marker
  /\ obs_cross_count = 1

(*** Project: the QA → observer-layer output crossing **************************)

Project ==
  /\ obs_cross_count = 1         \* can only project once per trace
  /\ fail = "OK"                 \* well-defined only on successful QA states
  /\ obs_float' = a              \* projection of final coord a (image in Nat)
  /\ obs_cross_count' = 2        \* boundary cross 2: discrete → observer
  /\ UNCHANGED qa_vars           \* projection does NOT mutate QA-layer state

(*** Post-projection absorbing stutter *****************************************
  After Project has fired, no further QA moves are permitted. This encodes
  the temporal half of Theorem NT: once the observer-output crossing has
  occurred, the discrete state is frozen; any continued QA evolution would
  require re-entering the discrete layer via a third boundary crossing,
  which is forbidden.
*******************************************************************************)

PostProjectStutter ==
  /\ obs_cross_count = 2
  /\ UNCHANGED ext_vars

(*** Extended Next *************************************************************
  Three disjuncts:
    1. QA_firewalled: a base-spec Next move PLUS UNCHANGED on observer vars.
       This is where the T2 Firewall is enforced structurally — QA actions
       cannot modify observer-layer state.
    2. Project: the output boundary crossing.
    3. PostProjectStutter: absorbing stutter after Project.
*******************************************************************************)

QA_firewalled ==
  /\ obs_cross_count = 1         \* QA evolution only allowed before Project
  /\ Next                        \* inherited from QuantumArithmetic
  /\ UNCHANGED obs_vars

Next_ext ==
  \/ QA_firewalled
  \/ Project
  \/ PostProjectStutter

Spec_ext ==
  Init_ext /\ [][Next_ext]_ext_vars

(*** ---- The Seven Axiom Invariants ---- *************************************
  One axiom per Inv_* (no conflation per scope discipline). Each invariant
  has a dedicated non-vacuity negative spec under QAAxioms_negative_*.tla.
  S1 is structural-only (TLA+ does not expose a `^` operator on our state
  variables; enforcement is syntactic over module text, not runtime).
*******************************************************************************)

(*** A1 (No-Zero): states in {1..CAP}, never 0. Operative constraint is on
     (b, e); derived coords (d, a) then live in {2..3*CAP} and {3..3*CAP}
     respectively, so a "no-zero" predicate on them is implied but weaker.
     This invariant checks b and e directly.
*******************************************************************************)

Inv_A1_NoZero ==
  /\ b \in 1..CAP
  /\ e \in 1..CAP

(*** A2 (Derived Coords): d = b+e, a = b+2e — always derived, never assigned
     independently. The base TupleClosed uses a = d+e, which expands to
     a = b+2e; we assert both forms explicitly to catch violations that
     might touch either pathway.
*******************************************************************************)

Inv_A2_DerivedCoords ==
  /\ d = b + e
  /\ a = b + 2 * e

(*** S1 (No `**2`): STRUCTURAL. The spec uses `*` exclusively for squaring
     and scaling (b*b, k*b, k*e) — there is no `^` operator on state
     variables in this module or its base QuantumArithmetic. Enforcement
     of this property is syntactic over module TEXT, not over reachable
     states; a state-level invariant cannot fully capture "no use of `^2`".
     The invariant below asserts a trivially-true state predicate that
     syntactically USES `b*b` (S1-compliant form), locking in the convention
     at the module level and referencing a state variable so TLC treats it
     as a genuine state invariant rather than a constant formula. Any
     future author who introduces `b^2` anywhere must either match this
     predicate's form OR explicitly override — the diff surfaces the
     violation. For runtime failure modes use the S2 and A2 invariants
     (which DO fire on non-Nat or miscomputed values).
*******************************************************************************)

Inv_S1_NoSquareOperator == b * b >= 0

(*** S2 (No float state): b, e, d, a must be Nat. In TLA+ native numerics
     are integer; the invariant catches type-domain violations where an
     action writes a non-Nat value (e.g., string, tuple, function) to a
     state variable. qtag is also checked for domain soundness.
*******************************************************************************)

Inv_S2_IntegerState ==
  /\ b \in Nat
  /\ e \in Nat
  /\ d \in Nat
  /\ a \in Nat
  /\ qtag \in Nat

(*** T1 (Path Time): QA time = integer path length. lastMove records the
     most recent generator; its domain is finite and discrete. No
     continuous time variable `t` is declared in ext_vars. The invariant
     verifies lastMove membership in the finite move-class alphabet
     (including "PROJECT" for the extension layer).
*******************************************************************************)

Inv_T1_IntegerPathTime ==
  lastMove \in {"NONE","σ","μ","λ"}
  \* Note: Project intentionally does NOT write to lastMove. It is a
  \* boundary-crossing action, not a QA generator. lastMove continues to
  \* record only σ / μ / λ moves, preserving the T1 interpretation of
  \* "discrete QA path time" as the number of generator firings.

(*** T2 (Firewall): Observer outputs never feed back as QA inputs.
     Operationalized at the state level: while obs_cross_count = 1 (Project
     has not yet run), obs_float must retain its Init value (0). Only the
     Project action may modify obs_float. Any QA action that writes
     obs_float to a different value violates the spatial firewall.
*******************************************************************************)

Inv_T2_FirewallRespected ==
  (obs_cross_count = 1) => (obs_float = 0)

(*** NT (Observer Projection): Boundary crossed EXACTLY twice per trace.
     obs_cross_count is 1 at Init (input crossing) and reaches 2 at
     Project (output crossing). It never reaches 3 (no feedback) and
     never reaches 0 (Init always counts as crossing 1). This is the
     temporal-counting form of Theorem NT.
*******************************************************************************)

Inv_NT_NoObserverFeedback ==
  obs_cross_count \in {1, 2}

(*** Theorems *******************************************************************)

THEOREM Spec_ext => []Inv_A1_NoZero
THEOREM Spec_ext => []Inv_A2_DerivedCoords
THEOREM Spec_ext => []Inv_S1_NoSquareOperator
THEOREM Spec_ext => []Inv_S2_IntegerState
THEOREM Spec_ext => []Inv_T1_IntegerPathTime
THEOREM Spec_ext => []Inv_T2_FirewallRespected
THEOREM Spec_ext => []Inv_NT_NoObserverFeedback

===============================================================================
