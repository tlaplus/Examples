------------------------ MODULE WellFoundedInduction ------------------------
(***************************************************************************)
(* This module contains useful theorems for inductive proofs and recursive *)
(* definitions based on a well-founded ordering.                           *)
(*                                                                         *)
(* Most of the statements of the theorems are decomposed in terms of       *)
(* definitions.  This is done for two reasons:                             *)
(*                                                                         *)
(*  - It makes it easier for the backends to instantiate the theorems      *)
(*    when those definitions are not expanded.  In fact, at the moment     *)
(*    the provers can't prove any of those theorems from the theorem       *)
(*    itself if the definitions are made usable.                           *)
(*                                                                         *)
(*  - It can be convenient when writing proofs to use those definitions    *)
(*    rather than having to write out their expansions.                    *)
(*                                                                         *)
(* A relation is represented as a set of ordered pairs, where we write     *)
(* <<x, y>> \in R instead of x R y.  It is more convenient to represent    *)
(* relations this way rather than as operators such as < .                 *)
(*                                                                         *)
(* Proofs of these theorems appear in module WellFoundedInduction_proofs.  *)
(***************************************************************************)
EXTENDS NaturalsInduction

(***************************************************************************)
(* The following defines what it means for a relation R to be transitively *)
(* closed on a set S.  In this and other definitions, we think of R as a   *)
(* relation on S, meaning that it is a subset of S \X S.  However, this is *)
(* not necessary.  Our results do not require this as a hypothesis, and it *)
(* is often convenient to apply them when R is a relation on a set         *)
(* containing S as a subset.  They're even true (though uninteresting) if  *)
(* R and S \X S are disjoint sets.                                         *)
(***************************************************************************)
IsTransitivelyClosedOn(R, S) ==
   \A i, j, k \in S : (<<i, j>> \in R)  /\ (<<j, k>> \in  R)  
                         => (<<i, k>> \in R)
(***************************************************************************)
(* If we think of R as a less-than relation, then R is well founded on S   *)
(* iff there is no "infinitely descending" sequence of elements of S.  The *)
(* canonical example of a well founded relation is the ordinary less-than  *)
(* relation on the natural numbers.                                        *)
(*                                                                         *)
(* A S with a well-founded ordering is often called well-ordered.          *)
(***************************************************************************)
IsWellFoundedOn(R, S) == 
    ~ \E f \in [Nat -> S] : \A n \in Nat : <<f[n+1], f[n]>> \in R

LEMMA EmptyIsWellFounded == \A S : IsWellFoundedOn({}, S)


LEMMA IsWellFoundedOnSubset ==
        ASSUME NEW R, NEW S, NEW T \in SUBSET S,
               IsWellFoundedOn(R,S)
        PROVE  IsWellFoundedOn(R,T)


LEMMA IsWellFoundedOnSubrelation ==
       ASSUME NEW S, NEW R, NEW RR, RR \cap (S \X S) \subseteq R,
              IsWellFoundedOn(R,S)
       PROVE  IsWellFoundedOn(RR,S)


(***************************************************************************)
(* If we think of R as a less-than relation on S, then the following is    *)
(* the set of elements of S that are less than x.                          *)
(***************************************************************************)
SetLessThan(x, R, S) ==  {y \in S : <<y, x>> \in R}

(***************************************************************************)
(* If we think of R as a less-than relation on S, then R is well-founded   *)
(* iff every non-empty subset of S has a minimal element.                  *)
(***************************************************************************)

THEOREM WFMin ==
         ASSUME NEW R, NEW S, 
                IsWellFoundedOn(R, S),
                NEW T, T \subseteq S, T # {}
         PROVE  \E x \in T : \A y \in T : ~ (<<y, x>> \in R)


THEOREM MinWF ==
         ASSUME NEW R, NEW S,
                \A T \in SUBSET S : T # {} => \E x \in T : \A y \in T : ~ (<<y, x>> \in R)
         PROVE  IsWellFoundedOn(R,S)


(***************************************************************************)
(* The two following lemmas are simple consequences of theorem WFMin.      *)
(***************************************************************************)
LEMMA WellFoundedIsIrreflexive ==
        ASSUME NEW R, NEW S, NEW x \in S,
               IsWellFoundedOn(R, S)
        PROVE  <<x, x>> \notin R


LEMMA WellFoundedIsAsymmetric ==
        ASSUME NEW R, NEW S, NEW x \in S, NEW y \in S,
               IsWellFoundedOn(R,S),
               <<x,y>> \in R, <<y,x>> \in R
        PROVE  FALSE


(***************************************************************************)
(* The following lemmas are simple facts about operator SetLessThan.       *)
(***************************************************************************)
LEMMA WFSetLessThanIrreflexive ==
        ASSUME NEW R, NEW S, NEW x \in S,
               IsWellFoundedOn(R,S)
        PROVE  x \notin SetLessThan(x,R,S)


LEMMA SetLessTransitive ==
        ASSUME NEW R, NEW S, NEW x \in S, NEW y \in SetLessThan(x,R,S),
               IsTransitivelyClosedOn(R, S)
        PROVE  SetLessThan(y, R, S) \subseteq SetLessThan(x, R, S)


----------------------------------------------------------------------------
(***************************************************************************)
(* The following theorem is the basis for proof by induction over a        *)
(* well-founded set.  It generalizes theorem GeneralNatInduction of module *)
(* NaturalsInduction.                                                      *)
(***************************************************************************)
THEOREM WFInduction ==
          ASSUME NEW P(_), NEW R, NEW S,
                 IsWellFoundedOn(R, S),
                 \A x \in S : (\A y \in SetLessThan(x, R, S) : P(y))
                    => P(x)
          PROVE  \A x \in S : P(x)


(***************************************************************************)
(* Theorem WFInductiveDef below justifies recursive definitions based on a *)
(* well-founded ordering.  We first prove it with the hypothesis that the  *)
(* ordering is transitively closed.  We prove the theorem for an arbitrary *)
(* well-founded relation by applying the special case to its transitive    *)
(* closure.                                                                *)
(***************************************************************************)
WFDefOn(R, S, Def(_,_)) == 
   \A g, h : 
      \A x \in S :
         (\A y \in SetLessThan(x, R, S) : g[y] = h[y])
           => (Def(g,x) = Def(h,x))

OpDefinesFcn(f, S, Def(_,_)) ==
   f =  CHOOSE g : g = [x \in S |-> Def(g, x)]

WFInductiveDefines(f, S, Def(_,_)) ==
     f = [x \in S |-> Def(f, x)]
                                          
WFInductiveUnique(S, Def(_,_)) ==
  \A g, h : /\ WFInductiveDefines(g, S, Def)
            /\ WFInductiveDefines(h, S, Def)
            => (g = h)

THEOREM WFDefOnUnique ==
          ASSUME NEW Def(_,_), NEW R, NEW S,
                 IsWellFoundedOn(R, S), WFDefOn(R, S, Def)
          PROVE  WFInductiveUnique(S, Def)


LEMMA WFInductiveDefLemma ==
        ASSUME NEW Def(_,_), NEW R, NEW S, NEW f,
               IsWellFoundedOn(R, S),
               IsTransitivelyClosedOn(R, S),
               WFDefOn(R, S, Def),
               OpDefinesFcn(f, S, Def)
        PROVE  WFInductiveDefines(f, S, Def)


(***************************************************************************)
(* The following defines the transitive closure of the relation R on S.    *)
(* More precisely, it is the transitive closure of the restriction of R    *)
(* to S.  We give an abstract definition of transitive closure as the      *)
(* smallest relation that contains R (restricted to S \X S) and that is    *)
(* transitively closed, then prove some relevant properties.               *)
(***************************************************************************)
TransitiveClosureOn(R,S) ==
   { ss \in S \X S : 
        \A U \in SUBSET (S \X S) :
           /\ R \cap S \X S \subseteq U
           /\ IsTransitivelyClosedOn(U, S)
           => ss \in U }  

LEMMA TransitiveClosureThm ==
         \A R, S : 
           /\ R \cap S \X S \subseteq TransitiveClosureOn(R, S)
           /\ IsTransitivelyClosedOn(TransitiveClosureOn(R, S), S)


LEMMA TransitiveClosureMinimal ==
        ASSUME NEW R, NEW S, NEW U \in SUBSET (S \X S),
               R \cap S \X S \subseteq U,
               IsTransitivelyClosedOn(U,S)
        PROVE  TransitiveClosureOn(R,S) \subseteq U


(***************************************************************************)
(* The following lemmas are consequences of the two previous ones. The     *)
(* first three state closure properties of transitive closure, the fourth  *)
(* lemma allows one to chop off a step in the underlying relation for any  *)
(* pair in the transitive closure.                                         *)
(***************************************************************************)

LEMMA TCTCTC ==
       ASSUME NEW R, NEW S, NEW i \in S, NEW j \in S, NEW k \in S,
              <<i,j>> \in TransitiveClosureOn(R,S),
              <<j,k>> \in TransitiveClosureOn(R,S)
       PROVE  <<i,k>> \in TransitiveClosureOn(R,S)


LEMMA TCRTC ==
       ASSUME NEW R, NEW S, NEW i \in S, NEW j \in S, NEW k \in S,
              <<i,j>> \in TransitiveClosureOn(R,S), <<j,k>> \in R
       PROVE  <<i,k>> \in TransitiveClosureOn(R,S)


LEMMA RTCTC ==
       ASSUME NEW R, NEW S, NEW i \in S, NEW j \in S, NEW k \in S,
              <<i,j>> \in R, <<j,k>> \in TransitiveClosureOn(R,S)
       PROVE  <<i,k>> \in TransitiveClosureOn(R,S)


LEMMA TransitiveClosureChopLast ==
        ASSUME NEW R, NEW S, NEW i \in S, NEW k \in S, <<i,k>> \in TransitiveClosureOn(R,S)
        PROVE  \E j \in S : /\ <<j,k>> \in R
                            /\ i = j \/ <<i,j>> \in TransitiveClosureOn(R,S)


THEOREM TransitiveClosureWF ==
          ASSUME NEW R, NEW S, IsWellFoundedOn(R,S)
          PROVE  IsWellFoundedOn(TransitiveClosureOn(R, S), S)


THEOREM WFInductiveDef ==
          ASSUME NEW Def(_,_), NEW R, NEW S, NEW f,
                 IsWellFoundedOn(R, S),
                 WFDefOn(R, S, Def),
                 OpDefinesFcn(f, S, Def)
          PROVE  WFInductiveDefines(f, S, Def)


(***************************************************************************)
(* Theorem WFInductiveDef allows us to conclude that a recursively defined *)
(* function satisfies its recursion equation.  The following result allows *)
(* us to deduce the range of this function.                                *)
(***************************************************************************)
THEOREM WFInductiveDefType == 
          ASSUME NEW Def(_,_), NEW f, NEW R, NEW S, NEW T,
                 T # {},
                 IsWellFoundedOn(R, S),
                 WFDefOn(R, S, Def),
                 WFInductiveDefines(f, S, Def),
                 \A g \in [S -> T], s \in S : Def(g, s) \in T
          PROVE  f \in [S -> T]

 
 ---------------------------------------------------------------------------- 
(***************************************************************************)
(* Below are some theorems that allow us to derive some useful             *)
(* well-founded relations from a given well-founded relation.  First, we   *)
(* define the operator OpToRel that constructs a relation (a set of        *)
(* ordered pairs) from a relation expressed as an operator.                *)
(***************************************************************************)
OpToRel(_\prec_, S) == {ss \in S \X S : ss[1] \prec ss[2]}

(***************************************************************************)
(* To construct well-founded relations from the less-than relation on the  *)
(* natural numbers, we first prove that it is well-founded.                *)
(***************************************************************************)
THEOREM NatLessThanWellFounded == IsWellFoundedOn(OpToRel(<,Nat), Nat)


(***************************************************************************)
(* The next definition would be easier to read if we used the TLA+         *)
(* construct {<<x, y>> \in T : ...  }.  However, TLAPS does not support     *)
(* that notation.  (It's meaning is rather complicated in the general case *)
(* when T is not a Cartesian product of sets.)                             *)
(***************************************************************************)
PreImage(f(_), S, R) == {ss \in S \X S : <<f(ss[1]), f(ss[2])>> \in R}

THEOREM PreImageWellFounded == 
          ASSUME NEW S, NEW T, NEW R, NEW f(_),
                 \A s \in S : f(s) \in T,
                 IsWellFoundedOn(R, T)
          PROVE  IsWellFoundedOn(PreImage(f, S, R), S)


(***************************************************************************)
(* We now prove that the lexicographical ordering on the Cartesian product *)
(* of two well-ordered sets is well-ordered.                               *)
(***************************************************************************)
LexPairOrdering(R1, R2, S1, S2) ==
     {ss \in (S1 \X S2) \X (S1 \X S2) : 
         \/ <<ss[1][1], ss[2][1]>> \in R1
         \/ /\ ss[1][1] = ss[2][1]
            /\ <<ss[1][2], ss[2][2]>> \in R2}
                           
THEOREM WFLexPairOrdering ==
          ASSUME NEW R1, NEW R2, NEW S1, NEW S2, 
                 IsWellFoundedOn(R1, S1),
                 IsWellFoundedOn(R2, S2)
          PROVE  IsWellFoundedOn(LexPairOrdering(R1, R2, S1, S2), S1 \X S2)


(***************************************************************************)
(* The preceding theorem generalizes in the obvious way to the Cartesian   *)
(* product of a finite number of well-ordered sets.  However, the          *)
(* statement of the general theorem is rather complicated, so we state it  *)
(* for the most useful case: the Cartesian product of n copies of the same *)
(* set.                                                                    *)
(***************************************************************************)
LexProductOrdering(R, S, n) ==
   { ff \in [1..n -> S] \X [1..n -> S] :
       \E j \in 1..n : 
          /\ \A i \in 1..(j-1) : ff[1][i] = ff[2][i]
          /\ <<ff[1][j], ff[2][j]>> \in R }

THEOREM WFLexProductOrdering ==
  ASSUME NEW R, NEW S, NEW n \in Nat,
         IsWellFoundedOn(R, S)
  PROVE  IsWellFoundedOn(LexProductOrdering(R, S, n), [1..n -> S])

=============================================================================
\* Modification History
\* Last modified Thu Feb 13 18:14:56 GMT-03:00 2014 by merz
\* Last modified Sun Jan 01 18:39:23 CET 2012 by merz
\* Last modified Wed Nov 23 10:13:18 PST 2011 by lamport
