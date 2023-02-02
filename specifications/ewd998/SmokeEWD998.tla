------------------------------- MODULE SmokeEWD998 -------------------------------
EXTENDS EWD998, TLC, Randomization, IOUtils, CSV, FiniteSets

\* In theory, TLC can check this spec exhaustively, but it is not feasible.
ASSUME TLCGet("config").mode \in {"generate", "simulate"}

k ==
    10

\* SmokeInit is configured to re-define the initial predicate. We use  SmokeInit
\* to randomly select a subset of the defined initial states in cases when the
\* set of all initial states is too expensive to generate during smoke testing.
SmokeInit ==
    \* First disjunct guarantees that there is always at least one initial state
    \* (Inv!P0 conjunct in second disjunct might exclude all initial states "defined"
    \* with RandomSubset).  Randomly choosing initial states from a large set of
    \* states could be provide by TLC's simulator.
    \/ /\ active = [n \in Node |-> TRUE]
       /\ color = [n \in Node |-> "black"]
       /\ counter = [i \in Node |-> 0]
       /\ pending = [i \in Node |-> 0]
       /\ token = [pos |-> 0, q |-> 0, color |-> ("black")]
    \/ /\ pending \in RandomSubset(k, [Node -> 0..(N-1)])
       /\ counter \in RandomSubset(k, [Node -> -(N-1)..(N-1)])
       /\ active \in RandomSubset(k, [Node -> BOOLEAN])
       /\ color \in RandomSubset(k, [Node -> Color])
       /\ token \in RandomSubset(k, [pos: Node, q: Node, color: ({"black"})])
       /\ Inv!P0 \* Reject states with invalid ratio between counter, pending, ...

\* StopAfter  has to be configured as a state constraint. It stops TLC after ~1
\* second or after generating 100 traces, whatever comes first, unless TLC
\* encountered an error.  In this case,  StopAfter  has no relevance.
StopAfter ==
    TLCGet("config").mode = "simulate" =>
    (* The smoke test has a time budget of 1 second. *)
    \/ TLCSet("exit", TLCGet("duration") > 1)
    (* Generating 100 traces should provide reasonable coverage. *)
    \/ TLCSet("exit", TLCGet("diameter") > 100)

BF ==
    CHOOSE s \in SUBSET (1..6) : ToString(s) = IOEnv.BF

PN ==
    CHOOSE s \in (1..10) : ToString(s) = IOEnv.PN

===============================================================================
