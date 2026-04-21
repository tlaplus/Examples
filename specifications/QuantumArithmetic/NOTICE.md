Attribution Notice
------------------

This package is extracted from the `signal_experiments` monorepo (Will
Dale, 2026) for submission to `github.com/tlaplus/examples`. The TLA+
logic (generator algebra, axiom invariants, non-vacuity specs) is
unchanged from its repo-internal canonical form; only the module
identifiers and file names were renamed (to `QuantumArithmetic` /
`QuantumArithmeticAxioms` / `QuantumArithmeticAxioms_negative_*`) to
match the naming conventions of the upstream `tlaplus/examples` corpus.
The MIT `LICENSE` in this directory governs use of the package; this
`NOTICE.md` records the requested citation form.

You may copy and reuse this construction and the accompanying TLC
configurations for research or teaching.

If you publish results that depend on:

  - the QARM generator semantics (sigma, mu, lambda_k with paired
    failure actions and absorbing-stutter on failure),
  - the duo-modular qtag packing `qtag = 24*phi9(a) + phi24(a)`,
  - the observer-layer firewall encoding (`obs_float`,
    `obs_cross_count`, `Project` action, `Inv_T2_FirewallRespected`,
    `Inv_NT_NoObserverFeedback`),
  - the specific invariant set (A1/A2/S1/S2/T1/T2/NT) as named here,
  - the paired non-vacuity discipline (one negative spec per
    runtime-checkable invariant, producing a minimal counterexample),

please cite:

  Dale, W. (2026). *Quantum Arithmetic Axiom System as TLA+ Temporal
  Invariants.* `github.com/tlaplus/examples/specifications/QuantumArithmetic`
  (extracted from the `signal_experiments` research monorepo).

and preserve:

  - the invariant names (`Inv_A1_NoZero`, etc.),
  - the observer-layer variable names (`obs_float`, `obs_cross_count`),
  - the `Project` action signature (writes `obs_cross_count' = 2`,
    reads `a`).

## References (primary)

- Lamport, L. (1994). *The Temporal Logic of Actions.* ACM TOPLAS 16(3),
  872-923. DOI: 10.1145/177492.177726.
- Lamport, L. (2002). *Specifying Systems: The TLA+ Language and Tools
  for Hardware and Software Engineers.* Addison-Wesley. ISBN
  978-0-321-14306-8.

These primary references are not subject to this attribution notice and
should be cited independently per their own terms.
