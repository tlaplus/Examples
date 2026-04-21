# Quantum Arithmetic — Axiom System as TLA+ Temporal Invariants

A self-contained TLA+ specification of the **Quantum Arithmetic (QA)**
generator algebra, with its six compliance axioms plus Theorem NT
(Observer Projection Firewall) encoded as TLA+ temporal invariants over
the reachable state graph. Each runtime-checkable invariant has a paired
non-vacuity spec that produces a minimal counterexample, mirroring the
proof-pair discipline common in the Paxos / distributed-snapshot
exemplars elsewhere in this corpus.

The package is **self-contained**: no external dependencies beyond the
TLA+ standard modules (`Naturals`, `Integers`, `TLC`). Reproducing every
result requires only `tla2tools.jar`.

---

## Why this might be interesting to TLA+ users

1. **First-class failure algebra.** Failures (`OUT_OF_BOUNDS`,
   `FIXED_Q_VIOLATION`, `ILLEGAL`) are modelled as absorbing-stutter
   state variables, not silent transition blocks. This gives TLC a
   concrete way to measure generator-set differentials on a
   failure-class-by-failure-class basis.

2. **Observer-projection firewall as temporal invariant.** Theorem NT
   of the QA axiom block asserts that the continuous–discrete
   boundary is crossed exactly twice per trace (input at `Init`, output
   at a dedicated `Project` action). This is encoded here with two
   observer-layer variables (`obs_float`, `obs_cross_count`) and two
   distinct invariants:
   - `Inv_T2_FirewallRespected` (spatial firewall — observer state
     immutable during discrete evolution)
   - `Inv_NT_NoObserverFeedback` (temporal bound — at most two
     boundary crossings).
   To our knowledge this is the first TLA+ encoding of a
   continuous–discrete firewall as a runtime-checkable property.

3. **Axiom hygiene.** Six of the seven invariants (A1, A2, S2, T1, T2, NT)
   have dedicated non-vacuity counterexample specs, so the positive
   result is demonstrably non-vacuous on each axiom. S1 (no `^2`
   operator on state variables) is structural and documented as such.

4. **Duo-modular packing.** The `qtag = 24 * phi9(a) + phi24(a)` packing
   puts `qtag` in `[0, 239]` and preserves both the mod-9 and mod-24
   invariants simultaneously — an efficient hash for TLC's fingerprint
   set and a research object in its own right.

---

## Background — one-paragraph QA

**Quantum Arithmetic** is a modular-arithmetic framework over pairs
`(b, e)` with derived coordinates `d = b + e` and `a = b + 2e`. Dynamics
live in the discrete integer layer; continuous functions enter only as
**observer projections** at the input and output boundaries. The system
uses three generator actions:

- **σ** (sigma): `e → e + 1`
- **μ** (mu):    swap `b ↔ e`
- **λ_k** (lambda): scale `(b, e) → (k·b, k·e)` for `k ∈ KSet`

Each generator is paired with explicit failure actions (`OUT_OF_BOUNDS`
when successor exceeds `CAP`, `FIXED_Q_VIOLATION` when successor breaks
duo-modular invariance). The failure states are absorbing — once in a
fail state, the tuple is frozen.

The six compliance axioms are:

| Axiom | Rule | Runtime check? |
|---|---|---|
| A1 | No-Zero: `b, e ∈ {1..CAP}` | Yes (`Inv_A1_NoZero`) |
| A2 | Derived Coords: `d = b+e`, `a = b+2e` | Yes (`Inv_A2_DerivedCoords`) |
| S1 | No `^2` operator; use `b*b` | Structural (module text) |
| S2 | Integer state: `b, e, d, a ∈ Nat` | Yes (`Inv_S2_IntegerState`) |
| T1 | Integer path time: discrete generator alphabet only | Yes (`Inv_T1_IntegerPathTime`) |
| T2 | Firewall: observer outputs don't feed back as QA inputs | Yes (`Inv_T2_FirewallRespected`) |

Plus **Theorem NT** (Observer Projection Firewall): boundary crossed
exactly twice per trace, encoded as `Inv_NT_NoObserverFeedback`.

---

## Module inventory

| File | Role |
|---|---|
| `QuantumArithmetic.tla` | Base generator algebra. σ/μ/λ_k actions + paired failure actions. A1-compliant Init (`b, e ∈ 1..CAP`). |
| `QuantumArithmetic.cfg` | Bounded model (`CAP = 20`, `KSet = {2, 3}`). |
| `QuantumArithmeticAxioms.tla` | EXTENDS the base. Adds observer-layer variables (`obs_float`, `obs_cross_count`) + `Project` action + the seven axiom invariants. |
| `QuantumArithmeticAxioms.cfg` | CAP=20 positive check, all 7 invariants active. |
| `QuantumArithmeticAxioms_cap24.cfg` | CAP=24 applied-domain scale check (mod-24). |
| `QuantumArithmeticAxioms_negative_A1.tla` | Non-vacuity: writes `b' = 0`, violates `Inv_A1_NoZero`. |
| `QuantumArithmeticAxioms_negative_A2.tla` | Non-vacuity: writes `d' ≠ b' + e'`, violates `Inv_A2_DerivedCoords`. |
| `QuantumArithmeticAxioms_negative_S2.tla` | Non-vacuity: writes `b' = "ghost"` (non-Nat), violates `Inv_S2_IntegerState`. |
| `QuantumArithmeticAxioms_negative_T1.tla` | Non-vacuity: writes `lastMove' = "t_continuous"` outside alphabet. |
| `QuantumArithmeticAxioms_negative_T2.tla` | Non-vacuity: writes `obs_float' = 42` during discrete step. |
| `QuantumArithmeticAxioms_negative_NT.tla` | Non-vacuity: increments `obs_cross_count` past 2. |
| `QuantumArithmeticAxioms_negative_*.cfg` | Paired configs (one per negative spec). |
| `LICENSE` | MIT license. |
| `NOTICE.md` | Attribution notice / requested citation form. |

8 TLA+ modules + 9 configs + 1 README + 1 LICENSE + 1 NOTICE = 20 files
(plus `manifest.json`).

---

## Reproduction

From this directory, with `tla2tools.jar` on the path (referenced here
by `$TLA2TOOLS`):

```bash
# Positive check: all 7 invariants hold over the reachable state graph.
# Expected: 90 initial states / 470 distinct / depth 3 / 0 errors / ~2 s.
java -XX:+UseParallelGC -jar $TLA2TOOLS -workers 4 -terse \
    -config QuantumArithmeticAxioms.cfg QuantumArithmeticAxioms.tla

# Applied-domain scale: same spec, CAP = 24 (mod-24 QA).
# Expected: 132 initial states / 686 distinct / 0 errors / ~2 s.
java -XX:+UseParallelGC -jar $TLA2TOOLS -workers 4 -terse \
    -config QuantumArithmeticAxioms_cap24.cfg QuantumArithmeticAxioms.tla

# Base spec (QARM generator algebra, without axiom layer).
# Expected: 90 initial states / 374 distinct / 0 errors / ~3 s.
java -XX:+UseParallelGC -jar $TLA2TOOLS -workers 4 -terse \
    -config QuantumArithmetic.cfg QuantumArithmetic.tla

# Six non-vacuity checks — each produces a 2-state counterexample
# for its target invariant.
for axiom in A1 A2 S2 T1 T2 NT; do
  echo "=== Non-vacuity: Inv_${axiom} ==="
  java -XX:+UseParallelGC -jar $TLA2TOOLS -workers 4 -terse \
      -config QuantumArithmeticAxioms_negative_${axiom}.cfg \
      QuantumArithmeticAxioms_negative_${axiom}.tla
done
```

---

## Expected results

| Spec / Config | States | Depth | Outcome |
|---|---|---|---|
| `QuantumArithmetic` @ CAP=20 | 90 init / 374 distinct | 2 | 0 errors (5 base invariants hold) |
| `QuantumArithmeticAxioms` @ CAP=20 | 90 init / 470 distinct | 3 | 0 errors (all 7 axiom invariants hold) |
| `QuantumArithmeticAxioms` @ CAP=24 | 132 init / 686 distinct | 3 | 0 errors |
| `QuantumArithmeticAxioms_negative_A1` | 2 | 2 | `Inv_A1_NoZero` violated (b'=0 counterexample) |
| `QuantumArithmeticAxioms_negative_A2` | 2 | 2 | `Inv_A2_DerivedCoords` violated (d'=99 ≠ b'+e') |
| `QuantumArithmeticAxioms_negative_S2` | 2 | 2 | `Inv_S2_IntegerState` fails to evaluate (b'="ghost" — string ∉ Nat) |
| `QuantumArithmeticAxioms_negative_T1` | 2 | 2 | `Inv_T1_IntegerPathTime` violated (lastMove' out of alphabet) |
| `QuantumArithmeticAxioms_negative_T2` | 2 | 2 | `Inv_T2_FirewallRespected` violated (obs_float' modified by QA step) |
| `QuantumArithmeticAxioms_negative_NT` | 2 | 2 | `Inv_NT_NoObserverFeedback` violated (3rd boundary crossing attempted) |

All counterexamples are minimal (Init + 1 step). The wall-time budget on
a 4-core commodity workstation (OpenJDK 21 + TLC) is under 30 s for
the full package including the scale test.

**Note on the S2 counterexample.** TLC reports
`Error: Evaluating invariant Inv_S2_IntegerState failed` (rather than the
more familiar "Invariant X is violated") because the successor-state
assignment `b' = "ghost"` produces a state on which the invariant's
`b \in Nat` predicate is undefined — TLC cannot decide whether a string
is a natural number. This is the expected outcome for a type-domain
violation: the invariant fails, but via an evaluation error rather than
a boolean violation. Either way, the negative spec demonstrates S2 is
non-vacuous.

---

## Design notes

### Why `EXTENDS` rather than a single monolithic module

`QuantumArithmeticAxioms.tla` `EXTENDS QuantumArithmetic` so that the
generator algebra and the axiom invariants are separable concerns. This
matches the upstream convention in `specifications/Paxos/` (where
`Paxos.tla` composes `Consensus.tla`) and lets the base be reused by
other extension modules (e.g., alternative axiom systems, or
domain-specific refinements at larger `CAP`).

### The `Project` action and the observer-layer variables

The base spec has no notion of a continuous/observer layer.
`QuantumArithmeticAxioms.tla` introduces two variables:

- `obs_float ∈ 0..(3·CAP)` — observer scalar. Set to `0` at `Init`
  (symbolic "input seed") and updated exactly once by the `Project`
  action to the current value of the QA coord `a`.
- `obs_cross_count ∈ {1, 2}` — number of boundary crossings so far.
  `1` at `Init` (input crossing); `2` after `Project` fires (output
  crossing). Reaching `3` would indicate observer-layer feedback into
  the discrete layer, which Theorem NT forbids.

The extended `Next_ext` has three disjuncts:

1. `QA_firewalled`: a base-spec `Next` move PLUS `UNCHANGED <<obs_float,
   obs_cross_count>>`. Only fires when `obs_cross_count = 1`.
2. `Project`: the output boundary crossing.
3. `PostProjectStutter`: absorbing after `Project`.

### Why `Inv_S1_NoSquareOperator` is `b * b >= 0`

TLA+ has no native `^2` or `**` operator on state variables in the
relevant modules; S1's "no libm-ULP-drift-prone squaring" rule is
**syntactic** over module text, not a state predicate over reachable
values. To keep all seven axioms as named invariants in a single
consistent stack, `Inv_S1_NoSquareOperator` is defined as the trivially
true state predicate `b * b >= 0`. This locks in the `b*b` convention at
the module level (any future author introducing `b^2` would diff against
this predicate) and satisfies TLC's preference for state invariants to
reference at least one state variable. The S1 enforcement at the *text*
level is handled by an external linter in the source repo.

---

## References

Primary TLA+ references:

- Lamport, L. (1994). *The Temporal Logic of Actions.* ACM Transactions
  on Programming Languages and Systems 16(3), 872–923. DOI:
  [10.1145/177492.177726](https://doi.org/10.1145/177492.177726).
- Lamport, L. (2002). *Specifying Systems: The TLA+ Language and Tools
  for Hardware and Software Engineers.* Addison-Wesley.
  ISBN 978-0-321-14306-8.
- Cousineau, D., Doligez, D., Lamport, L., Merz, S., Ricketts, D., &
  Vanzetto, H. (2012). *TLA+ Proofs.* FM 2012 (LNCS 7436), 147–154.

## License

MIT — see [`LICENSE`](LICENSE). Suggested citation form in
[`NOTICE.md`](NOTICE.md).
