---------------------------- MODULE MCReachability ----------------------------
EXTENDS Naturals, Sequences, TLC
(***************************************************************************)
(* High-level specification of a state-graph explorer that does NOT        *)
(* enforce BFS ordering.  The frontier S is a set and the next state       *)
(* to explore is chosen non-deterministically from S.                      *)
(***************************************************************************)

(***************************************************************************)
(* A (state) graph G is a directed graph represented by a record with      *)
(* 'states', 'initials', and 'actions' components.                         *)
(*                                                                         *)
(* The CommunityModules Graphs.tla module is not used here because its     *)
(* representation [node, edge] differs from ours: we use an adjacency      *)
(* function (actions \in [states -> SUBSET states]) rather than an         *)
(* explicit edge set (edge \subseteq node \X node), and carry a            *)
(* distinguished 'initials' component that Graphs.tla does not model.      *)
(***************************************************************************)
IsGraph(G) == /\ {"states", "initials", "actions"} = DOMAIN G
              /\ G.actions \in [G.states -> SUBSET G.states]
              /\ G.initials \subseteq G.states

(***************************************************************************)
(* Successor states of s, excluding self-loops.                            *)
(***************************************************************************)
SuccessorsOf(s, SG) == {t \in SG.actions[s] : t # s}

(***************************************************************************)
(* The predecessor of v in a spanning tree t (a set of                     *)
(* <<predecessor, successor>> pairs) is the first element of the           *)
(* unique pair whose second element equals v.                              *)
(***************************************************************************)
Predecessor(t, v) == (CHOOSE pair \in t : pair[2] = v)[1]

CONSTANT StateGraph, ViolationStates

ASSUME /\ IsGraph(StateGraph)
       /\ ViolationStates \subseteq StateGraph.states

VARIABLES S,              \* Frontier: set of states yet to explore
          C,              \* Set of visited states
          T,              \* Set of <<predecessor, successor>> pairs (spanning tree)
          L,              \* BFS level of each state that has been assigned a level
          successors,     \* Triples <<lvl, t, s>> still to process for the current
                          \* Explore step: t is the successor at BFS level lvl,
                          \* s is the predecessor that generated it.
          done,           \* TRUE after violation or deadlock detected
          counterexample \* Path from initial state to violation/deadlock state

vars == <<S, C, successors, done, T, counterexample, L>>

Init == /\ S = StateGraph.initials
        /\ C = {}
        /\ successors = {}
        /\ done = FALSE
        /\ T = {}
        /\ counterexample = <<>>
        /\ L = [s \in {} |-> 0]

---------------------------------------------------------------------------

(***************************************************************************)
(* Check an initial state for a safety violation.                          *)
(***************************************************************************)
InitCheck ==
    /\ ~done
    /\ successors = {}
    /\ \E s \in S \ C :
         /\ C' = C \cup {s}
         /\ L' = (s :> 0) @@ L
         /\ done' = (s \in ViolationStates)
         /\ counterexample' = IF s \in ViolationStates
                              THEN <<s>> ELSE counterexample
    /\ UNCHANGED <<S, successors, T>>

---------------------------------------------------------------------------

(***************************************************************************)
(* Pick any state from the frontier S for exploration.  The next state     *)
(* is chosen non-deterministically (\E s \in S), so no ordering is         *)
(* imposed on the exploration.  Predecessor pairs for all new successors   *)
(* are added to T here.                                                    *)
(***************************************************************************)
Explore ==
    /\ ~done
    /\ successors = {}
    /\ S \subseteq C
    /\ S # {}
    /\ \E s \in S :
         LET succs == SuccessorsOf(s, StateGraph) \ C
             lvl == L[s] + 1
         IN  /\ S' = S \ {s}
             /\ successors' = {<<lvl, t, s>> : t \in succs}
             /\ T' = T \cup {<<s, t>> : t \in succs}
             /\ done' = (SuccessorsOf(s, StateGraph) = {})
             /\ counterexample' = IF SuccessorsOf(s, StateGraph) = {}
                                  THEN <<s>> ELSE counterexample
    /\ UNCHANGED <<C, L>>

---------------------------------------------------------------------------

(***************************************************************************)
(* Process one successor: mark visited, add to frontier, check violation.  *)
(***************************************************************************)
Each ==
    /\ ~done
    /\ successors # {}
    /\ \E succ \in successors :
         /\ successors' = successors \ {succ}
         /\ C' = C \cup {succ[2]}
         /\ S' = S \cup {succ[2]}
         /\ L' = (succ[2] :> succ[1]) @@ L
         /\ done' = (succ[2] \in ViolationStates)
         /\ counterexample' = IF succ[2] \in ViolationStates
                              THEN <<succ[3], succ[2]>> ELSE counterexample
    /\ UNCHANGED T

---------------------------------------------------------------------------

(***************************************************************************)
(* Trace reconstruction: walk backward through T, prepending              *)
(* predecessors to the counterexample until an initial state is reached.   *)
(***************************************************************************)
Trc ==
    /\ done
    /\ counterexample # <<>>
    /\ Head(counterexample) \notin StateGraph.initials
    /\ counterexample' = <<Predecessor(T, Head(counterexample))>>
                          \o counterexample
    /\ UNCHANGED <<S, C, successors, done, T, L>>

---------------------------------------------------------------------------

Terminating == done /\ UNCHANGED vars

Next ==
    \/ InitCheck
    \/ Explore
    \/ Each
    \/ Trc
    \/ Terminating

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Next)

Termination == <>(done \/ (S = {} /\ successors = {}))

(***************************************************************************)
(* If violation states exist, the explorer eventually finds one and        *)
(* constructs a valid counterexample path from an initial state to it.     *)
(***************************************************************************)
Live == ViolationStates # {} =>
            <>[](/\ counterexample # <<>>
                 /\ counterexample[Len(counterexample)] \in ViolationStates
                 /\ counterexample[1] \in StateGraph.initials)

=============================================================================
