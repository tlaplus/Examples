----------------------------- MODULE BlockDagTest -----------------------------

(**************************************************************************************)
(* Tests for BlockDag operators using small concrete DAGs.                            *)
(**************************************************************************************)

EXTENDS FiniteSets, Sequences, Integers, TLC

N == {1, 2}
R == 1..3
Leader(r) == CASE
    r = 1 -> 1
[]  r = 2 -> 2
[]  r = 3 -> 1

INSTANCE BlockDag WITH N <- N, R <- R, Leader <- Leader

v11 == <<1, 1>> \* leader
v21 == <<2, 1>>
v12 == <<1, 2>>
v22 == <<2, 2>> \* leader
v13 == <<1, 3>> \* leader
v23 == <<2, 3>>

ASSUME TestNodeRound == Node(v12) = 1 /\ Round(v12) = 2

ASSUME TestLeaderVertice ==
    /\ LeaderVertex(1) = v11
    /\ LeaderVertex(2) = v22
    /\ LeaderVertex(3) = v13

ASSUME TestOrderSetPermutation ==
    LET SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}
        IsPermutation(seq, s) == SeqToSet(seq) = s /\ Len(seq) = Cardinality(s)
    IN  IsPermutation(OrderSet({v11, v21}), {v11, v21})

dag1 ==
    << {Genesis, v11, v21, v12, v22, v13, v23},
       {<<v11, Genesis>>, <<v21, Genesis>>, 
            <<v12, v21>>, <<v22, v11>>, <<v13, v22>>,
            <<v13, v21>>, <<v13, v12>>, <<v23, v22>>} >>

ASSUME TestPreviousLeader1 == PreviousLeader(dag1, 3) = v22
ASSUME TestPreviousLeader2 == PreviousLeader(dag1, 2) = v11 
ASSUME TestPreviousLeaderBase == PreviousLeader(dag1, 1) = <<>> 

ASSUME TestLinearize == Linearize(dag1, v13) =
    <<<<1, 1>>, <<2, 2>>>> \o OrderSet({<<2, 1>>, <<1, 2>>}) \o <<<<1, 3>>>>

=========================================================================
