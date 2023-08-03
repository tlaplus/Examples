-------------------------------- MODULE Util --------------------------------
EXTENDS Sequences, FiniteSets, Naturals, TLC
\* Simple utility functions
intersects(a, b) == (Cardinality(a \cap b) > 0)
max(s) == CHOOSE i \in s : (~\E j \in s : j > i)
min(s) == CHOOSE i \in s : (~\E j \in s : j < i)

\* Utilies from Practical TLA+
ReduceSet(op(_, _), set, acc) ==
  LET f[s \in SUBSET set] == \* here's where the magic is
    IF s = {} THEN acc
    ELSE LET x == CHOOSE x \in s: TRUE
         IN op(x, f[s \ {x}])
  IN f[set]
ReduceSeq(op(_, _), seq, acc) == 
  ReduceSet(LAMBDA i, a: op(seq[i], a), DOMAIN seq, acc)
\* Pulls an indice of the sequence for elem.
Index(seq, elem) == CHOOSE i \in 1..Len(seq): seq[i] = elem
\* end from Practical TLA+

Range(T) == { T[x] : x \in DOMAIN T }
    
SeqToSet(s) == {s[i] : i \in DOMAIN s}
Last(seq) == seq[Len(seq)]
IsEmpty(seq) == Len(seq) = 0
\* Remove all occurences of `elem` from `seq`
Remove(seq, elem) == SelectSeq(seq, LAMBDA e: e /= elem)

\* Dual to UNION on intersect
INTERSECTION(setOfSets) == ReduceSet(\intersect, setOfSets, UNION setOfSets)

\* Borrowed from Stephan Merz. TLA+ Case Study: A Resource Allocator. [Intern report] A04-R-101 || merz04a, 2004, 20 p. ffinria-00107809f
(* The set of permutations of a finite set, represented as sequences.  *)
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
       IF ss = {} THEN { << >> }
       ELSE LET ps == [ x \in ss |-> 
                        { Append(sq,x) : sq \in perms[ss \ {x}] } ]
            IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

\* Helper to write "unit test" ASSUMES which print when false
test(lhs, rhs) == lhs /= rhs => Print(<<lhs, " IS NOT ", rhs>>, FALSE)


=============================================================================
\* Modification History
\* Last modified Tue Jun 16 12:04:20 CEST 2020 by tim
\* Created Tue Apr 28 16:43:24 CEST 2020 by tim
