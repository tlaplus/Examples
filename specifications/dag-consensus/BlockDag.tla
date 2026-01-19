----------------------------- MODULE BlockDag -----------------------------

(**************************************************************************************)
(* In this specification we define notions on DAGs useful for DAG-based consensus     *)
(* protocols (which build DAGs of blocks)                                             *)
(**************************************************************************************)

EXTENDS FiniteSets, Sequences, Integers, Utils, Digraph, TLC

CONSTANTS
    N \* The set of all network nodes (not DAG nodes)
,   R \* The set of rounds
,   Leader(_) \* operator mapping each round to its leader

(**************************************************************************************)
(* For our purpose of checking safety and liveness, DAG vertices just consist of a   *)
(* node and a round.                                                                  *)
(**************************************************************************************)
V == N \times R \* the set of possible DAG vertices
Node(v) == v[1]
Round(v) == IF v = <<>> THEN 0 ELSE v[2] \* accomodates <<>> as default value

(**************************************************************************************)
(* Next we define leader vertices:                                                    *)
(**************************************************************************************)
LeaderVertex(r) == IF r > 0 THEN <<Leader(r), r>> ELSE <<>>
IsLeader(v) == LeaderVertex(Round(v)) = v
Genesis == <<>>
ASSUME IsLeader(Genesis) \* this should hold

(**************************************************************************************)
(* OrderSet(S) arbitrarily order the members of the set S.  Note that, in TLA+,       *)
(* `CHOOSE' is deterministic but arbitrary choice, i.e. `CHOOSE e \in S : TRUE' is    *)
(* always the same `e' if `S' is the same                                             *)
(**************************************************************************************)
RECURSIVE OrderSet(_)
OrderSet(S) == IF S = {} THEN <<>> ELSE
    LET e == CHOOSE e \in S : TRUE
    IN  Append(OrderSet(S \ {e}), e)
    
(**************************************************************************************)
(* PreviousLeader(dag, r) returns the leader vertex in dag whose round is the         *)
(* largest but smaller than r.  We assume that dag contains at least the genesis      *)
(* vertex.                                                                            *)
(**************************************************************************************)
PreviousLeader(dag, r) == CHOOSE l \in Vertices(dag) : 
    /\  IsLeader(l)
    /\  Round(l) = Max({Round(l2) : l2 \in 
            {l2 \in Vertices(dag) : IsLeader(l2) /\ Round(l2) < r}})

(**************************************************************************************)
(* Linearize a DAG. In a real blockchain we should use a topological ordering, but,   *)
(* for the purpose of ensuring agreement, an arbitrary ordering (as provided by       *)
(* OrderSet) is fine. This assume a DAG where all paths end with the Genesis          *)
(* vertex.                                                                            *)
(**************************************************************************************)
RECURSIVE Linearize(_, _)
Linearize(dag, l) == IF Vertices(dag) = {<<>>} THEN <<>> ELSE
    LET dagOfL == SubDag(dag, {l})
        prevL == PreviousLeader(dagOfL, Round(l))
        dagOfPrev == SubDag(dag, {prevL})
        remaining == Vertices(dagOfL) \ Vertices(dagOfPrev)
    IN  Linearize(dagOfPrev, prevL) \o OrderSet(remaining \ {l}) \o <<l>>

Compatible(s1, s2) == \* whether the sequence s1 is a prefix of the sequence s2, or vice versa
    \A i \in 1..Min({Len(s1), Len(s2)}) : s1[i] = s2[i]
=========================================================================
