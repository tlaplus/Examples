# Vortex DSE — slot admission, and set reconciliation over it

Author: Vasilis Nasopoulos

## The problem

When many parties submit items to a shared ordered log, something has to decide
which position each item takes. The usual answer is coordination: a leader
assigns positions, or the nodes vote on them. Either way the decision costs
message rounds, and a round cannot be faster than the signal travelling between
the parties. Across continents that floor is tens to hundreds of milliseconds
per round, so the number of rounds a protocol needs largely sets what it can
achieve.

The question these specifications come from is narrower than "can we avoid
consensus", and worth separating from it: **can a node decide whether to accept
an item without asking anyone?** If the decision is local, it costs no round.
Whether the accepted sets then agree across nodes is a second question, and the
two should not be conflated — the first module answers the first question, and
conflating them is exactly the error an earlier version of this file made.

## How it works

An item carries the slot it was stamped for. Each node keeps its own slot
counter and admits an item by comparing the two — a local predicate, evaluated
once, with no message sent and nobody consulted. There is no leader, no quorum
and no vote in the admission path.

Because the rule is the same everywhere and the stamp travels with the item,
two nodes applying it to the same item reach the same verdict without
communicating about it. That is the whole mechanism, and its modest size is the
point: what it buys is that admission adds no round trip, and what it does
*not* buy is agreement on the resulting sets, which needs its own layer and its
own argument.

Deciding locally raises three obligations, and they are what the modules
establish: that no node admits an item stamped for a slot it has not reached;
that no item is admitted twice, including across a crash; and that a stricter
variant of the rule can be adopted without reproving anything.

## Two admission rules

The rules differ by one operator, and both are specified because both exist.

| module | rule | meaning |
| --- | --- | --- |
| `Vortex_DSE_CSlot` | `m.cslot <= current_slot` | the default. An item stamped for slot *k* that arrives late is still admitted, into slot *k*. Nothing is dropped. |
| `Vortex_DSE_CSlot_TTL` | `m.cslot = current_slot` | an opt-in mode for bounded memory. An item that misses its slot is refused permanently, so state does not grow behind the frontier. |

The strict rule is a concession to memory, not a stronger protocol, and the
modules say so rather than assert it:

* `Vortex_DSE_CSlot_TTL_Proofs` proves `Spec => C!Spec` — the strict mode
  refines the default, so every safety property of the default is inherited
  rather than reproved. Equality is a stronger gate than `<=`; nothing else
  differs.
* `MC_Vortex_DSE_CSlot_TTL_admission.cfg` is a deliberate liveness failure.
  `EventualAdmission` holds under the default rule and fails here, because an
  item whose slot has passed is refused for good. That is the price of the
  strict rule, checked rather than described.

## What these modules do not cover

Stated plainly, because a reader should be able to tell what is proved from
what is merely present:

* **This is not a consensus protocol, and these modules do not model one.**
  What is here is local slot admission plus an idealized set reconciliation
  over it.
* **Delivery is a single global `network` set.** There is no per-node delivery
  state, no selective loss, no conflicting payloads under one id, no ordering
  within a slot, and no replicated application state.
* **`Reconcile` assigns the union in one atomic step.** Agreement is therefore
  a property of that action rather than something a reconciliation protocol
  establishes. The module is named for the layer it stands in for, not for a
  protocol it contains.
* **The TTL module never deletes anything.** Bounded memory is the entire
  reason that mode exists, and it is not modelled here; only what the strict
  rule refuses is.
* **`Vortex_DSE_CSlot_Skew` states an assumption, not a mechanism.** It bounds
  pairwise clock skew structurally, by forbidding any tick that would breach
  `MaxSkew`, and says nothing about what would maintain that bound.
* **Admission and agreement are not composed.** They are specified separately
  and not shown to hold together.

The implementation these specifications describe is not part of this
contribution, and no claim about its behaviour is made or checked here.

## Modules

| module | what it adds |
| --- | --- |
| `Vortex_DSE_CSlot` | admission, crash and rejoin via a persisted snapshot |
| `Vortex_DSE_CSlot_Proofs` | `TypeCorrect`, `NoFutureAdmissionCorrect` |
| `Vortex_DSE_CSlot_ExactlyOnce_Proof` | `StrictExactlyOnceCorrect` |
| `Vortex_DSE_CSlot_TTL` | the strict admission rule |
| `Vortex_DSE_CSlot_TTL_Proofs` | that the strict rule refines the default |
| `Vortex_DSE_CSlot_Skew` | a per-node clock in place of the global one, with forged slot stamps injected |
| `Vortex_DSE_CSlot_AE` | `Freeze`, `Reconcile`, `Commit` over the strict rule |
| `Vortex_DSE_CSlot_AE_Proofs` | deductive proofs for that layer |

`Vortex_DSE_CSlot_AE` is specified over the strict rule and is not a refinement
of the default one. Extending it to the late-tolerant rule means restating what
"no reordering across slots" should mean, which is not attempted here.

No specification carries a slot horizon: the ticker is unbounded and the
adversary may forge any slot in `Nat`. Horizons belong to model checking and
live in the `MC_` modules, which bound the actions directly rather than by state
constraint — under a constraint TLC evaluates invariants on the state that
crosses the boundary before discarding it, which is unsound for these
properties. `MaxSkew` is the one bound that stays in a specification, because it
is an assumption the protocol relies on rather than an artifact of checking.

## What is checked

Every TLAPS proof discharges under `tlapm --strict`, which fails on unproved
obligations and on steps left open; a plain `tlapm` invocation exits 0 in both
cases. There are no `OMITTED` steps.

| | obligations |
| --- | --- |
| `Vortex_DSE_CSlot_Proofs` | 23 |
| `Vortex_DSE_CSlot_ExactlyOnce_Proof` | 19 |
| `Vortex_DSE_CSlot_AE_Proofs` | 10 |
| `Vortex_DSE_CSlot_TTL_Proofs` | 34 |

Each module states one property of interest and marks the rest as corollaries
of it, rather than listing them flat in a way that suggests more is proved than
is. In the core that property is `NoFutureAdmission`; in the reconciliation
layer it is `ProcessedAreCurrentSlot` together with `CommittedIsUnion`.

Every model completes in a few seconds. `Vortex_DSE_CSlot_AE` carries Apalache
type annotations, but no symbolic model is registered; the models here are TLC
only.

## Where this sits

These modules are one part of a larger body of specifications, most of which is
not public. The rest covers what is listed above as absent — per-node clocks and
the mechanism that bounds their skew, lossy delivery, equivocation and
accountability, crash and rejoin composed with agreement, and the timing layer
that maintains the slot boundary.

That is context for why the pieces here look narrow, and nothing more. It is not
offered as evidence: a reviewer should not be asked to credit work they cannot
read, so nothing in this directory rests on it, and no property claimed here
depends on a module that is not present.

The conceptual treatment, with the motivation and the measurements from a
running implementation, is in the whitepaper:
<https://github.com/vasilisnasopoulos/vortex-dse-whitepaper> (CC BY-NC-ND 4.0).
