-------------------------------- MODULE Majority -----------------------------
(****************************************************************************)
(* TLA+ specification and proof of the majority vote algorithm due to Boyer *)
(* and Moore.                                                               *)
(* R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.          *)
(* In: R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody      *)
(* Bledsoe, pp. 105-117. Dordrecht, The Netherlands, 1991.                  *)
(* Originally published in a technical report from 1981.                    *)
(* The algorithm takes as input a sequence of values, makes one pass over   *)
(* the sequence, and reports an element cand such that no element other     *)
(* than cand may have an absolute majority in the sequence.                 *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Value
ASSUME ConstAssump == Value # {}

(****************************************************************************)
(* Although seq is an input to the algorithm, we make it a variable so that *)
(* we can use the model checker to verify the algorithm for all sequences   *)
(* up to some bounded size.                                                 *)
(****************************************************************************)
VARIABLES 
  seq,    \* input sequence of values, never changes 
  i,      \* next position of sequence to be checked
  cand,   \* current candidate for having a majority
  cnt     \* lower bound for the number of occurrences of the candidate so far

vars == <<seq, i, cand, cnt>>

TypeOK ==
    /\ seq \in Seq(Value)
    /\ i \in 1 .. Len(seq)+1
    /\ cand \in Value
    /\ cnt \in Nat

Init ==
    /\ seq \in Seq(Value)
    /\ i = 1
    /\ cand \in Value
    /\ cnt = 0

Next ==
    /\ i <= Len(seq)
    /\ i' = i+1 /\ seq' = seq
    /\ \/ /\ cnt = 0
          /\ cand' = seq[i]
          /\ cnt' = 1
       \/ /\ cnt # 0 /\ cand = seq[i]
          /\ cand' = cand
          /\ cnt' = cnt + 1
       \/ /\ cnt # 0 /\ cand # seq[i]
          /\ cand' = cand
          /\ cnt' = cnt - 1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(****************************************************************************)
(* Definitions used for stating correctness.                                *)
(****************************************************************************)
\* set of indexes in the prefix of the sequence strictly before j holding v
PositionsBefore(v,j) == { k \in 1 .. (j-1) : seq[k] = v }
\* number of times v occurs in that prefix
OccurrencesBefore(v,j) == Cardinality(PositionsBefore(v,j))
\* number of times v occurs in all of the sequence
Occurrences(x) == OccurrencesBefore(x, Len(seq)+1)

\* main correctness property: cand can be the only value that has a majority
Correct == 
    i > Len(seq) =>
    \A v \in Value : 2 * Occurrences(v) > Len(seq) => v = cand

\* inductive invariant for proving correctness
Inv ==
    /\ cnt <= OccurrencesBefore(cand, i)
    /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
    /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

==============================================================================
