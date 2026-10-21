------------------------------- MODULE StaleShrink -------------------------------
(***************************************************************************)
(* Safe contraction on stale views ("polite shrink"), for one sector that   *)
(* every node initially holds.                                              *)
(*                                                                          *)
(* N nodes each hold a shared resource.  Any of them may decide to stop     *)
(* holding it, but at least R must always remain: R-mutual inclusion.  No   *)
(* node asks permission.  A node announces that it intends to leave, waits  *)
(* D ticks on its own timer, then re-checks against its own view of the     *)
(* system, which is up to L ticks out of date, and either leaves, waits     *)
(* a tick, or withdraws.                                                    *)
(*                                                                          *)
(* The two re-check rules compared:                                         *)
(*  - "tb" (V3): count LOWER-id announcers as gone; leave if R remain.      *)
(*  - "patient" (V6): count EVERY other announcer as gone; leave if R       *)
(*    remain.  If not, and some higher-id announcer is racing and no lower  *)
(*    one is, keep the announcement and re-check next tick instead of       *)
(*    withdrawing.                                                          *)
(*                                                                          *)
(* STRUCTURE.  Each node acts alone, in its own steps: Announce(n) and      *)
(* Recheck(n).  A step reads only that node's own variables (whether it     *)
(* holds the sector, its timer intent[n], whether it has announced) and a   *)
(* view: a snapshot of the system published between 1 and L ticks ago,      *)
(* chosen afresh at every re-check, so a node's information can be a        *)
(* different age at each decision.  Time is modelled with an explicit       *)
(* clock, now, advanced by its own action, in the style of Abadi and        *)
(* Lamport's "old-fashioned recipe" for real time.  Nodes never read now:   *)
(* it stands for two timing assumptions, (1) whatever a node acts on is at  *)
(* most L ticks old (gossip delivers within a known bound: a synchronous    *)
(* timing assumption, not an asynchronous model), and (2) a node's timer    *)
(* fires after D ticks.  AdvanceTime is enabled only when no re-check is    *)
(* due, so timers fire on time.  When time advances, the current state is   *)
(* published: snapshots stands for what gossip has delivered.               *)
(*                                                                          *)
(* The rule depends on the bound L: a node deciding alone can only rule out *)
(* that a holder it still sees has already left if it knows how old its     *)
(* information can be.  Announcements are unconstrained (any holder may     *)
(* announce at any tick), so safety does not lean on the trigger.           *)
(*                                                                          *)
(* Expected results:                                                        *)
(*  - tb, N=4, R=1, L=2, D=4: Safety is VIOLATED by a staggered cascade:    *)
(*    nodes announce in descending id order a tick apart, each counts a     *)
(*    higher-id announcer as staying, and that announcer has left inside    *)
(*    its blind window.                                                     *)
(*  - patient, with D >= L: no error; and whenever anyone announced and a   *)
(*    copy could be spared, someone left (Progress).                        *)
(*  - patient with D < L: Safety is violated: no rule is safe when the      *)
(*    wait is shorter than the staleness.                                   *)
(* There are no deaths: every departure is a shrink, so Safety is "never    *)
(* fewer than R holders".                                                   *)
(*                                                                          *)
(* REFERENCES                                                               *)
(*  - Origin: dynamic storage-arc sizing in Holochain's kitsune2 DHT        *)
(*    (github.com/holochain/kitsune2/issues/160).  The rules, and the       *)
(*    Python checker and Rust implementation this spec mirrors, are in      *)
(*    github.com/ValiChord/polite-shrink (REPORT_stale_views.md).  As far   *)
(*    as we know, the rules are not published elsewhere.                    *)
(*  - The problem: H. Kakugawa, "Mutual inclusion in asynchronous message-  *)
(*    passing distributed systems", JPDC 77, 2015; S. Kamei and             *)
(*    H. Kakugawa, "An asynchronous message-passing distributed algorithm   *)
(*    for the global critical section problem", arXiv:1807.05674.  There   *)
(*    the problem is called l-mutual inclusion; their solutions use quorums *)
(*    and permission messages, this one uses neither.                       *)
(*  - Announce, wait, then decide: the doorway of Lamport's bakery          *)
(*    algorithm (CACM 17(8), 1974).                                         *)
(*  - Timing: M. Abadi and L. Lamport, "An old-fashioned recipe for real    *)
(*    time", TOPLAS 16(5), 1994; L. Lamport, "Real-time model checking is   *)
(*    really simple", CHARME 2005.                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes,    \* node ids, ordered naturals, e.g. 1..4
          R,        \* minimum number of holders
          L,        \* maximum age of a view, in ticks
          D,        \* wait between announcing and re-checking, in ticks
          Rule      \* "tb" (V3) or "patient" (V6)

ASSUME /\ Nodes \subseteq Nat /\ Nodes # {}
       /\ R \in Nat /\ L \in Nat \ {0} /\ D \in Nat \ {0}
       /\ Rule \in {"tb", "patient"}

\* Announcements may happen in ticks 0..Span-1: enough to cover every
\* relative offset between announcements, waits and view ages that matters.
Span == D + 2 * L + 1
\* Room for every intent to resolve, including V6's waiting.
Horizon == Span + D + 2
           + (IF Rule = "patient" THEN Cardinality(Nodes) * (D + 2 * L + 2) ELSE 0)

VARIABLES now,        \* the clock (nodes never read it; see STRUCTURE)
          holds,      \* nodes holding the sector
          intent,     \* intent[n]: tick at which n re-checks; 0 = none
          announced,  \* nodes that have announced (each announces once)
          snapshots   \* the last (up to) L published <<holders, announcers>>,
                      \* oldest first; the last entry is tick now-1

vars == <<now, holds, intent, announced, snapshots>>

TypeOK == /\ now \in 0..Horizon
          /\ holds \subseteq Nodes
          /\ intent \in [Nodes -> 0..(Horizon + D)]
          /\ announced \subseteq Nodes
          /\ Len(snapshots) <= L
          /\ \A i \in 1..Len(snapshots) :
                snapshots[i] \in (SUBSET Nodes) \X (SUBSET Nodes)

Announcers == { n \in Nodes : intent[n] # 0 }

Init == /\ now = 0
        /\ holds = Nodes
        /\ intent = [n \in Nodes |-> 0]
        /\ announced = {}
        /\ snapshots = << >>

\* A view of age a (1 <= a <= L): the state published at tick now - a.
\* snapshots holds ticks max(0, now-L)..now-1, so when now >= a the index
\* Len(snapshots) - a + 1 is valid.  Before tick a nothing older exists yet,
\* and the initial state is seen.
View(a) == IF now >= a
           THEN snapshots[Len(snapshots) - a + 1]
           ELSE <<Nodes, {}>>

\* n's decision on a view: "go", "wait" or "withdraw".
Decide(n, view) ==
    LET hs     == view[1]
        its    == view[2]
        lower  == { m \in its : m < n }
        higher == { m \in its : m > n }
    IN IF Rule = "tb"
       THEN IF Cardinality((hs \ {n}) \ lower) >= R THEN "go" ELSE "withdraw"
       \* eff: the holders n sees other than itself, counting every other
       \* announcer as already gone.  It is what n can rely on staying.
       ELSE LET eff == Cardinality((hs \ {n}) \ (its \ {n}))
            IN IF eff >= R THEN "go"
               ELSE IF higher # {} /\ lower = {} THEN "wait"
               ELSE "withdraw"

\* n announces that it intends to leave, and sets its timer.
Announce(n) ==
    /\ now < Span
    /\ n \in holds
    /\ n \notin announced
    /\ intent' = [intent EXCEPT ![n] = now + D]
    /\ announced' = announced \cup {n}
    /\ UNCHANGED <<now, holds, snapshots>>

\* n's timer fires: it re-checks on a view of some age a in 1..L.
Recheck(n) ==
    /\ n \in holds
    /\ intent[n] = now
    /\ intent[n] # 0
    /\ \E a \in 1..L :
          LET d == Decide(n, View(a))
          IN /\ holds' = IF d = "go" THEN holds \ {n} ELSE holds
             /\ intent' = [intent EXCEPT ![n] = IF d = "wait" THEN now + 1 ELSE 0]
    /\ UNCHANGED <<now, announced, snapshots>>

\* Time advances once every re-check due now has happened; the state at the
\* end of the tick is published.
AdvanceTime ==
    /\ now < Horizon
    /\ \A n \in holds : intent[n] # now \/ intent[n] = 0
    /\ now' = now + 1
    /\ snapshots' = LET s == Append(snapshots, <<holds, Announcers>>)
                    IN IF Len(s) > L THEN Tail(s) ELSE s
    /\ UNCHANGED <<holds, intent, announced>>

Done == now = Horizon /\ UNCHANGED vars

Next == \/ \E n \in Nodes : Announce(n) \/ Recheck(n)
        \/ AdvanceTime
        \/ Done

Spec == Init /\ [][Next]_vars

\* Never fewer than R holders (no deaths here, so any loss is a shrink's).
Safety == Cardinality(holds) >= R

\* At the end, if anyone announced and a copy could be spared, someone left.
Progress == (now = Horizon /\ announced # {} /\ Cardinality(Nodes) > R)
                => holds # Nodes
=============================================================================
