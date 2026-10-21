# StaleViewShrink: safe contraction on stale views

N nodes each hold a shared resource (here, one sector of a distributed hash
table). Any of them may decide to stop holding it, but at least R must always
remain. That is *l-mutual inclusion*, the mirror image of k-exclusion. There is
no coordinator. A node announces that it intends to leave, waits `D` ticks,
then re-checks against its own view of the world, which is up to `L` ticks old.

The spec compares two re-check rules (`Rule` in the `.cfg`):

- **`"tb"`, lowest-ID tie-break:** count lower-ID announcers as already gone;
  leave if R would remain.
- **`"patient"`, "patient lowest":** count *every* other announcer as already
  gone; leave if R would remain. If not, and only higher-ID announcers are
  racing, keep the announcement and re-check next tick instead of withdrawing.

## Why it is instructive

An earlier model of the same protocol let each node read the *current* holder
set atomically at re-check. Under that assumption both rules pass, and so does a
bare re-check with no tie-break at all. Giving nodes stale views changes the
verdict:

| model | rule | wait | result |
|---|---|---|---|
| `StaleShrink.cfg` | patient | 1× the max lag | no error (`Safety` and `Progress`) |
| `StaleShrinkV6Wait2x.cfg` | patient | 2× | no error |
| `StaleShrinkV3Cascade.cfg` | tb | 2× | **`Safety` violated** |
| `StaleShrinkV6TooShort.cfg` | patient | 0.5× | **`Safety` violated** (control) |

The tie-break fails to a **staggered cascade**: nodes 4, 3, 2 and 1 announce a
tick apart, in descending ID order, all two ticks stale. Each counts a higher-ID
announcer as staying, and that announcer has already left inside its blind
window. The last copy goes at tick 7. The patient rule never relies on a node
that might itself be leaving. It is safe whenever the wait is at least the
maximum lag, and it always lets someone leave. No rule is safe when the wait is
shorter than the lag, which is what the control shows.

There are no crashes in this spec. The source repository,
<https://github.com/ValiChord/polite-shrink>, has an exhaustive Python checker
that agrees with every verdict here and adds a crash at any tick. It also has a
Rust implementation, including a forced run of the cascade on a real (in-memory)
network.

Written by Ceri John with AI assistance (Claude, Anthropic). Apache-2.0, as in
the source repository.
