------------------------------- MODULE StaleShrink -------------------------------
(***************************************************************************)
(* Polite shrink with STALE views, for one sector held by every node.      *)
(*                                                                          *)
(* PoliteShrink.tla lets a node execute against the CURRENT holder set,     *)
(* read atomically.  Under that assumption even a bare re-check is safe, so *)
(* it cannot tell the shrink rules apart.  This spec gives each node a view *)
(* of the world as it was Lag[n] ticks ago, which is what the rules exist   *)
(* to survive.  It is the TLA+ form of spec/timed_check.py and follows its  *)
(* semantics tick for tick:                                                 *)
(*                                                                          *)
(*  - Time advances in ticks.  Each tick: (1) every intent due this tick    *)
(*    is re-checked, all against views from earlier ticks, so same-tick     *)
(*    decisions cannot see each other; (2) any holder that has not yet      *)
(*    announced may announce, executing D ticks later; (3) the tick's       *)
(*    holders and intenders are published to History.                      *)
(*  - A node's view at tick t is the state published at tick t - Lag[n]    *)
(*    (the initial state if that is before tick 0).  Lag is per node,       *)
(*    chosen nondeterministically from 1..L, so heterogeneous staleness is  *)
(*    covered.  Only the last L published states can ever be read, so only  *)
(*    those are kept.                                                       *)
(*  - Announcement is unconstrained (any tick, any subset), as in           *)
(*    PoliteShrink.tla: safety must not lean on the trigger being right.    *)
(*                                                                          *)
(* The two re-check rules:                                                  *)
(*  - "tb" (V3): count LOWER-id intenders as gone; vacate if R remain.      *)
(*  - "patient" (V6): count EVERY other intender as gone; vacate if R       *)
(*    remain.  If not, and some higher-id intender is racing and no lower   *)
(*    one is, keep the intent and re-check next tick instead of standing    *)
(*    down.                                                                 *)
(*                                                                          *)
(* Expected results (the same as timed_check.py):                           *)
(*  - tb, N=4, R=1, L=2, D=4: Safety is VIOLATED by a staggered cascade:    *)
(*    nodes announce in descending id order a tick apart, each counts a     *)
(*    higher-id announcer as staying, and that announcer has left inside    *)
(*    its blind window.                                                     *)
(*  - patient, same constants (and any D >= L): no error; and whenever      *)
(*    anyone announced, someone vacated (Progress).                         *)
(*                                                                          *)
(* No deaths in this spec: every departure is a shrink, so Safety is        *)
(* "never fewer than R holders".                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes,    \* node ids, ordered naturals, e.g. 1..4
          R,        \* redundancy target
          L,        \* maximum view lag, in ticks
          D,        \* wait between announcing and re-checking, in ticks
          Rule      \* "tb" (V3) or "patient" (V6)

ASSUME /\ Nodes \subseteq Nat /\ Nodes # {}
       /\ R \in Nat /\ L \in Nat \ {0} /\ D \in Nat \ {0}
       /\ Rule \in {"tb", "patient"}

\* Announcements may happen in ticks 0..Span-1: enough to cover every
\* relative offset that matters (as in timed_check.py).
Span == D + 2 * L + 1
\* Room for every intent to resolve, including V6's waiting.
Horizon == Span + D + 2
           + (IF Rule = "patient" THEN Cardinality(Nodes) * (D + 2 * L + 2) ELSE 0)

VARIABLES t,          \* current tick
          lag,        \* lag[n]: node n's view lag (fixed per behaviour)
          holds,      \* nodes holding the sector
          intent,     \* intent[n]: tick at which n re-checks; 0 = none
          announced,  \* nodes that have announced (each announces once)
          recent      \* the last (up to) L published <<holders, intenders>>,
                      \* oldest first; the last entry is tick t-1

vars == <<t, lag, holds, intent, announced, recent>>

Intenders(f) == { n \in Nodes : f[n] # 0 }

Init == /\ t = 0
        /\ lag \in [Nodes -> 1..L]
        /\ holds = Nodes
        /\ intent = [n \in Nodes |-> 0]
        /\ announced = {}
        /\ recent = << >>

\* Node n's view at tick t: the state published at tick t - lag[n].
View(n) == IF t >= lag[n]
           THEN recent[Len(recent) - lag[n] + 1]
           ELSE <<Nodes, {}>>

\* The decision for a due intent: "go", "wait" or "cancel".
Decide(n) ==
    LET hs   == View(n)[1]
        its  == View(n)[2]
        lower  == { m \in its : m < n }
        higher == { m \in its : m > n }
    IN IF Rule = "tb"
       THEN IF Cardinality((hs \ {n}) \ lower) >= R THEN "go" ELSE "cancel"
       ELSE LET eff == Cardinality((hs \ {n}) \ (its \ {n}))
            IN IF eff >= R THEN "go"
               ELSE IF higher # {} /\ lower = {} THEN "wait"
               ELSE "cancel"

Tick ==
    /\ t < Horizon
    /\ LET due    == { n \in holds : intent[n] # 0 /\ intent[n] = t }
           go     == { n \in due : Decide(n) = "go" }
           wait   == { n \in due : Decide(n) = "wait" }
           holds1 == holds \ go
           intent1 == [n \in Nodes |->
                         IF n \in wait THEN t + 1
                         ELSE IF n \in due THEN 0
                         ELSE intent[n]]
           eligible == IF t < Span
                       THEN { n \in holds1 : n \notin announced /\ intent1[n] = 0 }
                       ELSE {}
       IN \E ann \in SUBSET eligible :
            LET intent2 == [n \in Nodes |->
                              IF n \in ann THEN t + D ELSE intent1[n]]
            IN /\ holds' = holds1
               /\ intent' = intent2
               /\ announced' = announced \cup ann
               /\ recent' = LET r == Append(recent, <<holds1, Intenders(intent2)>>)
                            IN IF Len(r) > L THEN Tail(r) ELSE r
               /\ t' = t + 1
               /\ UNCHANGED lag

Done == t = Horizon /\ UNCHANGED vars

Next == Tick \/ Done

Spec == Init /\ [][Next]_vars

TypeOK == /\ t \in 0..Horizon
          /\ holds \subseteq Nodes
          /\ announced \subseteq Nodes
          /\ intent \in [Nodes -> 0..(Horizon + D)]

\* Never fewer than R holders (no deaths here, so any loss is a shrink's).
Safety == Cardinality(holds) >= R

\* At the end, if anyone announced and a copy could be spared, someone left.
Progress == (t = Horizon /\ announced # {} /\ Cardinality(Nodes) > R)
                => holds # Nodes
=============================================================================
