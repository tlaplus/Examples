------------------------ MODULE DiningPhilosophers_stats ------------------------
(***************************************************************************)
(* Estimate the average number of eating philosophers per state.  TLC      *)
(* generates random behaviors of DiningPhilosophers and sums over their    *)
(* states.  The spec does not model time, so states stand in for it.  A    *)
(* solution with fewer steps per meal thus has more eating states.         *)
(***************************************************************************)
EXTENDS DiningPhilosophers, TLC

ASSUME
    /\ TLCGet("config").mode = "generate"
    \* TLC's registers are local to a worker.
    /\ TLCGet("config").worker = 1
    \* Register 1 sums the eating philosophers, register 2 counts the states.
    /\ TLCSet(1, 0)
    /\ TLCSet(2, 0)

\* The conjunct keeps TLC from splitting Next into subactions, which reduces
\* the bias of -generate: https://github.com/tlaplus/tlaplus/issues/1485
StatsNext == Next /\ TRUE

Stats ==
    /\ TLCSet(1, TLCGet(1) + Cardinality({p \in P : IsEating(p)}))
    /\ TLCSet(2, TLCGet(2) + 1)

\* The average is eating / states.
PrintStats ==
    PrintT([eating |-> TLCGet(1), states |-> TLCGet(2)])
=============================================================================

Check out the commit of a solution, then run:

$ tlc DiningPhilosophers_stats -generate num=1000 -depth 1000
