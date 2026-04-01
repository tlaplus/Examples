---------------------------- MODULE StateGraphs ----------------------------
EXTENDS Sequences, Integers, IOUtils
(***************************************************************************)
(* Definitions of directed state graphs and their violation sets, used     *)
(* for testing model-checker specifications (TLCMC, MCReachability).       *)
(***************************************************************************)

\* Graph 1.
G1 == [states |-> 1..4,
       initials |-> {1,2},
       actions  |-> << {1,2}, {1,3}, {4}, {3} >>
       ]
V1 == {4}

\* Graph 1a.
G1a == [states |-> 1..4,
       initials |-> {3},
       actions  |-> << {1, 2}, {1, 3}, {4}, {3} >>]
\* Graph-wise it's impossible to reach state 1 from state 3
V1a == {1}

\* Graph 2. This graph is actually a forest of two graphs
\*    {1,2} /\ {3,4,5}. {1,2} are an SCC.
G2 == [states |-> 1..5,
       initials |-> {1,3},
       actions  |-> << {1, 2}, {1}, {4, 5}, {}, {} >> ]
V2 == {2,5}      

\* Graph 3.       
G3 == [states |-> 1..4,
       initials |-> {2},
       actions  |-> << {1,2}, {2,3}, {3,4}, {1,4} >> ]
V3 == {1}
      
\* Graph 4.
G4 == [states |-> 1..9,
       initials |-> {1,2,3},
       actions  |-> << {3}, {4}, {5}, {6}, {7}, {7}, {8, 9}, {}, {4} >> ]
V4 == {8}
      
\* Graph 5.
G5 == [states |-> 1..9,
       initials |-> {9},
       actions  |-> << {4,2}, {3}, {4}, {5}, {6}, {7}, {8}, {9}, {2} >> ]
V5 == {8}

\* Graph 6.
G6 == [states |-> 1..5,
       initials |-> {5},
       actions  |-> << {2,4,5}, {2}, {1}, {4}, {3} >> ]
V6 == {2}

\* Graph Medium (node 22 is a sink)
G7 == [states |-> 1..50,
       initials |-> {1},
       actions  |-> << {8,35},{15,46,22,23,50},{20,26,34},{5,18,28,37,43},{18,28},{44},{14,29},{42,45},{20,49},{10,12,31,47},
       {1,8,29,30,35,42},{22,31},{10,12,22,27},{23,24,48},{9,22,49},{9,35,50},{10},{21,25,39},{7,29,33,43},{16,41},{},
       {4,36,39,47},{7},{12,22,23},{5,6,39,44},{3,35},{10,13,17},{6,25,33,32,43},{23,30,40,45},{23,50},{24,38},
       {19,33},{6,7,14,38,48},{3,9,20},{3,20,41},{10,38,47},{21,43},{6,10,36,48},{36,38,39},{19,43},{16},
       {29,45},{32},{38,39},{40},{9,15,16,50},{17},{24,31},{13,22,34},{35,23,50} >> ]
V7 == {50}

\* Graph 8.
G8 == [states |-> 1..4,
       initials |-> {1},
       actions |-> <<{1,2},{2,3},{3,4},{4}>>]
V8 == {}

\* Graph 9.
G9 == [states |-> {1},
       initials |-> {1},
       actions |-> <<{1}>>]
V9 == {1}

\* Graph 10.
G10 == [states |-> {},
       initials |-> {},
       actions |-> <<>>]
V10 == {}

\* Graph 11.
G11 == [states |-> 1..10,
       initials |-> {},
       actions |-> << {}, {}, {}, {}, {}, {}, {}, {}, {}, {} >>]
V11 == {}

\* Graph 12.
G12 == [states |-> 1..3,
       initials |-> {1,2,3},
       actions |-> <<{},{},{}>>]
V12 == {1}

\* Graph 13 (simple sequence).
G13 == [states |-> 1..3,
       initials |-> {1},
       actions |-> <<{2},{3},{}>>]
V13 == {}

-----------------------------------------------------------------------------

GraphName == IF "GRAPH" \in DOMAIN IOEnv THEN IOEnv.GRAPH ELSE "7"

TestCase == CASE GraphName = "1"  -> [g |-> G1,  v |-> V1]
              [] GraphName = "1a" -> [g |-> G1a, v |-> V1a]
              [] GraphName = "2"  -> [g |-> G2,  v |-> V2]
              [] GraphName = "3"  -> [g |-> G3,  v |-> V3]
              [] GraphName = "4"  -> [g |-> G4,  v |-> V4]
              [] GraphName = "5"  -> [g |-> G5,  v |-> V5]
              [] GraphName = "6"  -> [g |-> G6,  v |-> V6]
              [] GraphName = "7"  -> [g |-> G7,  v |-> V7]
              [] GraphName = "8"  -> [g |-> G8,  v |-> V8]
              [] GraphName = "9"  -> [g |-> G9,  v |-> V9]
              [] GraphName = "10" -> [g |-> G10, v |-> V10]
              [] GraphName = "11" -> [g |-> G11, v |-> V11]
              [] GraphName = "12" -> [g |-> G12, v |-> V12]
              [] GraphName = "13" -> [g |-> G13, v |-> V13]

=============================================================================
