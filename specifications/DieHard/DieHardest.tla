----------------------------- MODULE DieHardest ------------------------------
(***************************************************************************)
(* Given two jug configurations that can each solve the Die Hard problem,  *)
(* which one reaches the Goal in fewer steps?                              *)
(*                                                                         *)
(* This is a question about pairs of behaviors — one from each             *)
(* configuration — rather than about a single behavior.  Such properties   *)
(* are called hyperproperties; ours is a 2-hyperproperty because it        *)
(* relates two behaviors.  Ordinary model checkers like TLC check trace    *)
(* properties (properties of individual behaviors), not hyperproperties.   *)
(* The standard workaround is self-composition: run two copies of the      *)
(* system side by side and reduce the hyperproperty to an ordinary         *)
(* invariant of the product system.  This module does exactly that by      *)
(* composing two instances of DieHarder.                                   *)
(*                                                                         *)
(* The choice of how the two copies advance matters.  Sections 1–3 show    *)
(* that the natural choice — parallel (lock-step) composition — has a      *)
(* subtle flaw: TLC's BFS finds the shortest trace for the slower          *)
(* configuration but not necessarily for the faster one.  Two fixes are    *)
(* explored; one works but departs from the logic of TLA+.  Section 4     *)
(* gives a clean solution: interleaved composition, where each instance    *)
(* steps independently.                                                    *)
(*                                                                         *)
(* Primary use case: show that adding a redundant jug (e.g. comparing      *)
(* <<5, 3>> against <<5, 3, 3>> for Goal = 4) can shorten the solution.    *)
(*                                                                         *)
(* References:                                                             *)
(*  - Lamport, "Verifying Hyperproperties With TLA", 2021.                 *)
(*    (https://ieeexplore.ieee.org/document/9505222)                       *)
(*  - Wayne, "Hypermodeling Hyperproperties", 2020                         *)
(*    (https://hillelwayne.com/post/hyperproperties/).                     *)
(***************************************************************************)
EXTENDS Naturals, Functions, FiniteSetsExt, TLC

(***************************************************************************)
(* The Die Hard problem has a solution iff: (1) the Goal fits in the       *)
(* largest jug, and (2) the Goal is divisible by the GCD of all jug        *)
(* capacities.  Condition (2) follows from Bézout's identity: the          *)
(* measurable quantities with jugs of capacities c1, …, cn are exactly     *)
(* the multiples of GCD(c1, …, cn).  The LET definitions use distinct      *)
(* names to avoid clashes with operators in DieHarder.                     *)
(***************************************************************************)
HasSolution(capacity, goal) ==
    LET Div(d, n) == \E k \in 0..n : n = d * k
        CDivisors(S) == {d \in 1..Min(S) : \A n \in S : Div(d, n)}
        GCD(S) == IF S = {} THEN 0 ELSE Max(CDivisors(S))
    IN /\ goal <= Max(Range(capacity))
       /\ Div(GCD(Range(capacity) \ {0}), goal)

CONSTANT Capacities,  \* <<Cap1, Cap2>>: a tuple of two jug-capacity functions.
         Goal         \* The target quantity of water.

(***************************************************************************)
(* TLC only guarantees strict BFS with a single worker.  Strict BFS is     *)
(* required so that counterexamples are shortest paths, and Section 3      *)
(* additionally depends on TLCSet/TLCGet registers that assume             *)
(* single-threaded exploration.                                            *)
(***************************************************************************)
ASSUME /\ TLCGet("config").mode = "bfs"
       /\ TLCGet("config").worker = 1

ASSUME Capacities[1] # Capacities[2]

ASSUME /\ HasSolution(Capacities[1], Goal)
       /\ HasSolution(Capacities[2], Goal)

VARIABLE c1,  \* Jug contents for configuration 1.
         c2,  \* Jug contents for configuration 2.
         s1,  \* Number of transitions taken by configuration 1.
         s2   \* Number of transitions taken by configuration 2.
vars == <<c1, c2, s1, s2>>

D1 == INSTANCE DieHarder WITH Jug <- DOMAIN Capacities[1],
                               Capacity <- Capacities[1],
                               Goal <- Goal,
                               contents <- c1

D2 == INSTANCE DieHarder WITH Jug <- DOMAIN Capacities[2],
                               Capacity <- Capacities[2],
                               Goal <- Goal,
                               contents <- c2

Init ==
    /\ D1!Init
    /\ D2!Init
    /\ s1 = 0
    /\ s2 = 0
-----------------------------------------------------------------------------
(***************************************************************************)
(* SECTION 1.  Parallel composition                                        *)
(*                                                                         *)
(* Both instances step in lock-step: every transition advances both.       *)
(*                                                                         *)
(* Flaw: TLC's BFS guarantees the shortest trace to the state where the    *)
(* last instance reaches the Goal.  The first instance's path in           *)
(* that trace may contain unnecessary detours and need not be its own      *)
(* shortest path.                                                          *)
(*                                                                         *)
(* Running example (used throughout Sections 1–3):                         *)
(*   Goal = 2, Cap1 = {j1:9, j2:10}, Cap2 = {j1:1, j2:3}                   *)
(*   Cap1's shortest solution: 6 steps.  Cap2's: 2 steps.                  *)
(*                                                                         *)
(* With NextParallel, TLC produces the 6-step trace below.  Cap1's path    *)
(* is its shortest (6 non-stuttering steps), but Cap2's path has 4 non-    *)
(* stuttering steps — not its shortest 2 (fill j2, pour j2→j1).            *)
(*                                                                         *)
(*  c1               c2                                                    *)
(*  [j1=0, j2=0]    [j1=0, j2=0]   initial                                 *)
(*  [j1=0, j2=10]   [j1=1, j2=0]                                           *)
(*  [j1=9, j2=1]    [j1=1, j2=0]   c2 stutters                             *)
(*  [j1=0, j2=1]    [j1=1, j2=0]   c2 stutters                             *)
(*  [j1=1, j2=0]    [j1=0, j2=0]   c2 goes backwards (empties j1)          *)
(*  [j1=1, j2=10]   [j1=0, j2=3]                                           *)
(*  [j1=9, j2=2]    [j1=1, j2=2]   both reach Goal = 2                     *)
(***************************************************************************)
NextParallel ==
    /\ D1!Next
    /\ D2!Next
    /\ UNCHANGED <<s1, s2>>

(***************************************************************************)
(* SECTION 2.  Parallel with per-behavior freeze                           *)
(*                                                                         *)
(* Once a behavior of an instance reaches the Goal, take no more steps.    *)
(* This is a per-behavior constraint, but TLC's BFS still generates all    *)
(* behaviors, including those in which the faster instance takes detours   *)
(* to keep pace with the slower one.  Constraining each behavior           *)
(* individually does not eliminate suboptimal paths to the Goal.  (TLC     *)
(* produces the same suboptimal path for Cap2 as in Section 1.)            *)
(***************************************************************************)
NextParallelFreeze ==
    /\ IF Goal \in Range(c1) THEN UNCHANGED c1 ELSE D1!Next
    /\ IF Goal \in Range(c2) THEN UNCHANGED c2 ELSE D2!Next
    /\ UNCHANGED <<s1, s2>>

(***************************************************************************)
(* SECTION 3.  Parallel with global BFS-level freeze                       *)
(*                                                                         *)
(* Use TLC's (global) registers to record the BFS depth at which each      *)
(* instance first reaches the Goal, then freeze the instance once the      *)
(* current depth exceeds that bound.  This correctly finds the globally    *)
(* shortest path for both instances: the freeze threshold is set by        *)
(* the global BFS exploration (which discovers the minimum depth), not     *)
(* by the particular behavior being explored.                              *)
(*                                                                         *)
(* For the running example, TLC now produces:                              *)
(*  c1               c2                                                    *)
(*  [j1=0, j2=0]    [j1=0, j2=0]   initial                                 *)
(*  [j1=0, j2=10]   [j1=0, j2=3]                                           *)
(*  [j1=9, j2=1]    [j1=1, j2=2]   c2 reaches Goal (2 steps) ←             *)
(*  [j1=0, j2=1]    [j1=1, j2=2]   c2 frozen                               *)
(*  [j1=1, j2=0]    [j1=1, j2=2]   c2 frozen                               *)
(*  [j1=1, j2=10]   [j1=1, j2=2]   c2 frozen                               *)
(*  [j1=9, j2=2]    [j1=1, j2=2]   c1 reaches Goal (6 steps) ←             *)
(*                                                                         *)
(* Both paths are individually shortest.  However, TLCSet and TLCGet       *)
(* are TLC-specific operators outside the logic of TLA+, making this       *)
(* approach incompatible with other TLA+ tools (e.g. Apalache).            *)
(***************************************************************************)
ASSUME TLCSet(2, 999) /\ TLCSet(3, 999)

NextParallelGlobalFreeze ==
    /\ IF TLCGet("level") >= TLCGet(2) THEN UNCHANGED c1 ELSE D1!Next
    /\ IF TLCGet("level") >= TLCGet(3) THEN UNCHANGED c2 ELSE D2!Next
    /\ Goal \in Range(c1') /\ TLCGet(2) = 999 => TLCSet(2, TLCGet("level") + 1)
    /\ Goal \in Range(c2') /\ TLCGet(3) = 999 => TLCSet(3, TLCGet("level") + 1)
    /\ UNCHANGED <<s1, s2>>

(***************************************************************************)
(* SECTION 4.  Interleaved (sequential) composition                        *)
(*                                                                         *)
(* Each instance steps independently: every transition advances exactly    *)
(* one instance.  TLC's BFS explores all interleavings and finds the       *)
(* shortest combined trace, whose length equals the sum of the two         *)
(* individual shortest paths.  In the counterexample, s1 and s2 give       *)
(* each configuration's step count.                                        *)
(*                                                                         *)
(* This works because the two instances share no state: any path for one   *)
(* can be freely combined with any path for the other.  BFS therefore      *)
(* individually minimizes both s1 and s2.                                  *)
(***************************************************************************)
NextInterleaved ==
    \/ D1!Next /\ UNCHANGED <<c2, s2>> /\ s1' = s1 + 1
    \/ D2!Next /\ UNCHANGED <<c1, s1>> /\ s2' = s2 + 1

Spec == Init /\ [][NextInterleaved]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* NotSolved holds as long as the two configurations have not both         *)
(* reached the Goal.  A counterexample — a behavior in which both          *)
(* configurations solve the problem — reveals the answer: the final        *)
(* state's s1 and s2 values show each configuration's step count.          *)
(*                                                                         *)
(* The ASSUMEs above guarantee that TLC will find a shortest               *)
(* counterexample.                                                         *)
(***************************************************************************)
NotSolved ==
    ~ (Goal \in Range(c1) /\ Goal \in Range(c2))
=============================================================================
