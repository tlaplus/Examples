----------------------------- MODULE Quicksort -----------------------------
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* If you are not already familiar with that algorithm, you should look it *)
(* up on the Web and understand how it works--including what the partition *)
(* procedure does, without worrying about how it does it.  The version     *)
(* presented here does not specify a partition procedure, but chooses in a *)
(* single step an arbitrary value that is the result that any partition    *)
(* procedure may produce.                                                  *)
(*                                                                         *)
(* The module also has a structured informal proof of Quicksort's partial  *)
(* correctness property--namely, that if it terminates, it produces a      *)
(* sorted permutation of the original sequence.  As described in the note  *)
(* "Proving Safety Properties", the proof uses the TLAPS proof system to   *)
(* check the decomposition of the proof into substeps, and to check some   *)
(* of the substeps whose proofs are trivial.                               *)
(*                                                                         *)
(* The version of Quicksort described here sorts a finite sequence of      *)
(* integers.  It is one of the examples in Section 7.3 of "Proving Safety  *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems, FiniteSetTheorems
  (*************************************************************************)
  (* This statement imports some standard modules, including ones used by  *)
  (* the TLAPS proof system.                                               *)
  (*************************************************************************)

(***************************************************************************)
(* To aid in model checking the spec, we assume that the sequence to be    *)
(* sorted are elements of a set Values of integers.                        *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* We define PermsOf(s) to be the set of permutations of a sequence s of   *)
(* integers.  In TLA+, a sequence is a function whose domain is the set    *)
(* 1..Len(s).  A permutation of s is the composition of s with a           *)
(* permutation of its domain.  It is defined as follows, where:            *)
(*                                                                         *)
(*  - Automorphisms(S) is the set of all permutations of S, if S is a      *)
(*    finite set--that is all functions f from S to S such that every      *)
(*    element y of S is the image of some element of S under f.            *)
(*                                                                         *)
(*  - f ** g  is defined to be the composition of the functions f and g.   *)
(*                                                                         *)
(* In TLA+, DOMAIN f is the domain of a function f.                        *)
(***************************************************************************)
Automorphisms(S) == { f \in [S -> S] : 
                        \A y \in S : \E x \in S : f[x] = y }

f ** g == [x \in DOMAIN g |-> f[g[x]]]

PermsOf(s) == { s ** f : f \in Automorphisms(DOMAIN s) }

LEMMA AutomorphismsCompose ==
    ASSUME NEW S, NEW f \in Automorphisms(S), NEW g \in Automorphisms(S)
    PROVE  f ** g \in Automorphisms(S)
BY DEF Automorphisms, **

LEMMA PermsOfLemma ==
    ASSUME NEW T, NEW s \in Seq(T), NEW t \in PermsOf(s)
    PROVE  /\ t \in Seq(T)
           /\ Len(t) = Len(s)
           /\ \A i \in 1 .. Len(s) : \E j \in 1 .. Len(s) : t[i] = s[j]
           /\ \A i \in 1 .. Len(s) : \E j \in 1 .. Len(t) : t[j] = s[i]
BY DOMAIN t = DOMAIN s DEF PermsOf, Automorphisms, **

LEMMA PermsOfPermsOf ==
    ASSUME NEW T, NEW s \in Seq(T), NEW t \in PermsOf(s), NEW u \in PermsOf(t)
    PROVE  u \in PermsOf(s)
<1>1. PICK f \in Automorphisms(DOMAIN s) : t = s ** f
  BY DEF PermsOf
<1>2. PICK g \in Automorphisms(DOMAIN t) : u = t ** g
  BY DEF PermsOf
<1>3. DOMAIN t = DOMAIN s 
  BY PermsOfLemma
<1>4. f ** g \in Automorphisms(DOMAIN s)
  BY <1>3, AutomorphismsCompose
<1>5. u = s ** (f ** g)
  BY <1>1, <1>2, <1>3, Zenon DEF Automorphisms, **
<1>. QED  BY <1>4, <1>5 DEF PermsOf

(**************************************************************************)
(* We define Max(S) and Min(S) to be the maximum and minimum,             *)
(* respectively, of a finite, non-empty set S of integers.                *)
(**************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

LEMMA MinIsMin == 
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x <= y
    PROVE  x = Min(S)
BY DEF Min

LEMMA MaxIsMax == 
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x >= y
    PROVE  x = Max(S)
BY DEF Max

LEMMA NonemptyMin ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S
    PROVE  /\ Min(S) \in S 
           /\ Min(S) <= x
<1>. DEFINE P(T) == T \in SUBSET Int =>
                      /\ T # {} => Min(T) \in T
                      /\ \A y \in T : Min(T) <= y
<1>1. P({})
  OBVIOUS
<1>2. ASSUME NEW T, NEW y, y \notin T, P(T)
      PROVE  P(T \cup {y})
  <2>. HAVE T \cup {y} \in SUBSET Int
  <2>1. CASE T = {}
    <3>1. y = Min(T \cup {y})
      BY <2>1 DEF Min
    <3>. QED  BY <2>1, <3>1
  <2>2. CASE T # {}
    <3>1. CASE y < Min(T)
      <4>1. /\ y \in T \cup {y}
            /\ \A z \in T \cup {y} : y <= z
        BY <1>2, <3>1
      <4>2. y = Min(T \cup {y})
        BY <4>1 DEF Min
      <4>. QED  BY <4>1, <4>2
    <3>2. CASE ~(y < Min(T))
      <4>. DEFINE mn == Min(T)
      <4>1. /\ mn \in T \cup {y}
            /\ \A z \in T \cup {y} : mn <= z
        BY <1>2, <2>2, <3>2
      <4>. HIDE DEF mn
      <4>2. mn = Min(T \cup {y})
        BY <4>1 DEF Min
      <4>. QED  BY <4>1, <4>2
    <3>. QED  BY <3>1, <3>2
  <2>. QED  BY <2>1, <2>2
<1>3. \A T : IsFiniteSet(T) => P(T)
  <2>. HIDE DEF P
  <2>. QED  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED BY <1>3

LEMMA NonemptyMax ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S
    PROVE  /\ Max(S) \in S
           /\ x <= Max(S)
<1>. DEFINE P(T) == T \in SUBSET Int =>
                      /\ T # {} => Max(T) \in T
                      /\ \A y \in T : y <= Max(T)
<1>1. P({})
  OBVIOUS
<1>2. ASSUME NEW T, NEW y, y \notin T, P(T)
      PROVE  P(T \cup {y})
  <2>. HAVE T \cup {y} \in SUBSET Int
  <2>1. CASE T = {}
    <3>1. y = Max(T \cup {y})
      BY <2>1 DEF Max
    <3>. QED  BY <2>1, <3>1
  <2>2. CASE T # {}
    <3>1. CASE y > Max(T)
      <4>1. /\ y \in T \cup {y}
            /\ \A z \in T \cup {y} : y >= z
        BY <1>2, <3>1
      <4>2. y = Max(T \cup {y})
        BY <4>1 DEF Max
      <4>. QED  BY <4>1, <4>2
    <3>2. CASE ~(y > Max(T))
      <4>. DEFINE mx == Max(T)
      <4>1. /\ mx \in T \cup {y}
            /\ \A z \in T \cup {y} : z <= mx
        BY <1>2, <2>2, <3>2
      <4>. HIDE DEF mx
      <4>2. mx = Max(T \cup {y})
        BY <4>1 DEF Max
      <4>. QED  BY <4>1, <4>2
    <3>. QED  BY <3>1, <3>2
  <2>. QED  BY <2>1, <2>2
<1>3. \A T : IsFiniteSet(T) => P(T)
  <2>. HIDE DEF P
  <2>. QED  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED BY <1>3

LEMMA IntervalMinMax ==
    ASSUME NEW i \in Int, NEW j \in Int, i <= j
    PROVE  i = Min(i .. j) /\ j = Max(i .. j)
BY DEF Min, Max

(***************************************************************************)
(* The operator Partitions is defined so that if I is an interval that's a *)
(* subset of 1..Len(s) and p \in Min(I) ..  Max(I)-1, the Partitions(I, p, *)
(* seq) is the set of all new values of sequence seq that a partition      *)
(* procedure is allowed to produce for the subinterval I using the pivot   *)
(* index p.  That is, it's the set of all permutations of seq that leaves  *)
(* seq[i] unchanged if i is not in I and permutes the values of seq[i] for *)
(* i in I so that the values for i =< p are less than or equal to the      *)
(* values for i > p.                                                       *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) : 
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i \in I : \E j \in I : t[i] = s[j]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

LEMMA PartitionsLemma ==
    ASSUME NEW T, NEW s \in Seq(T), NEW I \in SUBSET (1 .. Len(s)),
           NEW p \in I, NEW t \in Partitions(I, p, s)
    PROVE  /\ t \in Seq(T)
           /\ Len(t) = Len(s)
           /\ \A i \in (1 .. Len(s)) \ I : t[i] = s[i]
           /\ \A i \in I : \E j \in I : t[i] = s[j]
           /\ \A i,j \in I : i <= p /\ p < j => t[i] <= t[j]
BY PermsOfLemma DEF Partitions

(***************************************************************************)
(* Our algorithm has three variables:                                      *)
(*                                                                         *)
(*    seq  : The array to be sorted.                                       *)
(*                                                                         *)
(*    seq0 : Holds the initial value of seq, for checking the result.      *)
(*                                                                         *)
(*    U : A set of intervals that are subsets of 1..Len(seq0), an interval *)
(*        being a nonempty set I of integers that equals Min(I)..Max(I).   *)
(*        Initially, U equals the set containing just the single interval  *)
(*        consisting of the entire set 1..Len(seq0).                       *)
(*                                                                         *)
(* The algorithm repeatedly does the following:                            *)
(*                                                                         *)
(*    - Chose an arbitrary interval I in U.                                *)
(*                                                                         *)
(*    - If I consists of a single element, remove I from U.                *)
(*                                                                         *)
(*    - Otherwise:                                                         *)
(*        - Let I1 be an initial interval of I and I2 be the rest of I.    *)
(*        - Let newseq be an array that's the same as seq except that the  *)
(*          elements seq[x] with x in I are permuted so that               *)
(*          newseq[y] =< newseq[z] for any y in I1 and z in I2.            *)
(*        - Set seq to newseq.                                             *)
(*        - Remove I from U and add I1 and I2 to U.                        *)
(*                                                                         *)
(* It stops when U is empty.  Below is the algorithm written in PlusCal.   *)
(***************************************************************************)
 
(***************************************************************************
--fair algorithm Quicksort {
  variables  seq \in Seq(Values) \ {<< >>}, seq0 = seq,  U = {1..Len(seq)};
  { a: while (U # {}) 
        { with (I \in U) 
            { if (Cardinality(I) = 1) 
                { U := U \ {I} } 
              else 
                { with (p \in Min(I) .. (Max(I)-1),
                        I1 = Min(I)..p,
                        I2 = (p+1)..Max(I),
                        newseq \in Partitions(I, p, seq))
                    { seq := newseq ;
                      U := (U \ {I}) \cup {I1, I2} }      }  }  }  }  }

****************************************************************************)
(***************************************************************************)
(* Below is the TLA+ translation of the PlusCal code.                      *)
(***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES seq, seq0, U, pc

vars == << seq, seq0, U, pc >>

Init == (* Global variables *)
        /\ seq \in Seq(Values) \ {<< >>}
        /\ seq0 = seq
        /\ U = {1..Len(seq)}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF U # {}
           THEN /\ \E I \in U:
                     IF Cardinality(I) = 1
                        THEN /\ U' = U \ {I}
                             /\ seq' = seq
                        ELSE /\ \E p \in Min(I) .. (Max(I)-1):
                                  LET I1 == Min(I)..p IN
                                    LET I2 == (p+1)..Max(I) IN
                                      \E newseq \in Partitions(I, p, seq):
                                        /\ seq' = newseq
                                        /\ U' = ((U \ {I}) \cup {I1, I2})
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << seq, U >>
     /\ seq0' = seq0

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
----------------------------------------------------------------------------
(***************************************************************************)
(* PCorrect is the postcondition invariant that the algorithm should       *)
(* satisfy.  You can use TLC to check this for a model in which Seq(S) is  *)
(* redefined to equal the set of sequences of at elements in S with length *)
(* at most 4.  A little thought shows that it then suffices to let Values  *)
(* be a set of 4 integers.                                                 *)
(***************************************************************************)
PCorrect == (pc = "Done") => 
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q] 

(***************************************************************************)
(* Below are some definitions leading up to the definition of the          *)
(* inductive invariant Inv used to prove the postcondition PCorrect.  The  *)
(* partial TLA+ proof follows.  As explained in "Proving Safety            *)
(* Properties", you can use TLC to check the level-<1> proof steps.  TLC   *)
(* can do those checks on a model in which all sequences have length at    *)
(* most 3.                                                                 *)
(***************************************************************************)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions == {DP \in SUBSET SUBSET (1..Len(seq0)) :
                      /\ (UNION DP) = 1..Len(seq0)
                      \* /\ \A I \in DP : I = Min(I)..Max(I)
                      /\ \A I \in DP : \E mn,mx \in 1 .. Len(seq0) : I = mn .. mx
                      /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])
 
TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
          /\ pc \in {"a", "Done"}

Inv == /\ TypeOK
       /\ (pc = "Done") => (U = {})
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2>1. TypeOK
    <3>1. seq \in Seq(Values) \ {<<>>} 
      BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
    <3>2. seq0 \in Seq(Values) \ {<<>>}
      BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
    <3>3. U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
      <4>1. Len(seq0) \in Nat  /\ Len(seq0) > 0
        BY <3>1, EmptySeq, LenProperties DEF Init
      <4>2. 1..Len(seq0) # {}
        BY <4>1
      <4>3. QED
       BY <4>2, U = {1..Len(seq0)} DEF Init
    <3>4. pc \in {"a", "Done"}
      BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF TypeOK   
  <2>2. pc = "Done" => U = {}
    BY DEF Init
  <2>3. UV \in DomainPartitions
    BY DEF Init, UV, DomainPartitions
  <2>4. seq \in PermsOf(seq0)
    <3>1. seq \in PermsOf(seq)
      <4>. DEFINE f == [i \in 1 .. Len(seq) |-> i]
      <4>. /\ f \in [DOMAIN seq -> DOMAIN seq]
           /\ \A y \in DOMAIN seq : \E x \in DOMAIN seq : f[x] = y
        BY DEF Init
      <4>. QED  BY DEF Init, PermsOf, Automorphisms, **
    <3>2. QED
      BY <3>1 DEF Init
  <2>5. UNION UV = 1..Len(seq0)
    BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
  <2>6. \A I, J \in UV : (I # J) => RelSorted(I, J)
    BY DEF Init, Inv, TypeOK, DomainPartitions, RelSorted, UV
  <2>7. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE a
    <3> USE <2>1
    <3>1. CASE U # {}
      <4>1. /\ pc = "a"
            /\ pc' = "a"
        BY <3>1 DEF a
      <4>2. PICK I \in U : a!2!2!1!(I)
        (*******************************************************************)
        (* a!2!2!1(I) is the formula following `\E I \in U:' in the        *)
        (* definition of a.                                                *)
        (*******************************************************************)
        BY <3>1 DEF a
      <4>3. CASE Cardinality(I) = 1
        <5>1. /\ U' = U \ {I}
              /\ seq' = seq
              /\ seq0' = seq0
          BY <4>2, <4>3 DEF a
        <5>. IsFiniteSet(I)
          <6>. IsFiniteSet(1 .. Len(seq0))
            BY FS_Interval DEF Inv, TypeOK
          <6>. I \subseteq 1 .. Len(seq0)
            BY DEF Inv, TypeOK
          <6>. QED  BY FS_Subset
        <5>j. PICK j : I = {j}
          BY <4>3, FS_Singleton
        <5>2. QED
          <6>1. UV' = UV
            (***************************************************************)
            (* The action removes a singleton set {j} from U, which adds j *)
            (* to the set {{i} : i \in 1..Len(seq) \ UNION U}, thereby     *)
            (* keeping it in UV.                                           *)
            (***************************************************************)
            <7>1. j \in 1 .. Len(seq)
              BY <5>j, PermsOfLemma DEF Inv, TypeOK
            <7>2. \A J \in U : I # J => j \notin J
              BY <5>j, Zenon DEF Inv, TypeOK, DomainPartitions, UV
            <7>. QED  BY <5>1, <5>j, <7>1, <7>2 DEF UV
          <6>2. TypeOK'
            BY <4>1, <4>3, <5>1 
            DEF Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
          <6>3. ((pc = "Done") => (U = {}))'
            BY <4>1, <4>3, <5>1 
            DEF Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
          <6>4. (UV \in DomainPartitions)'
            BY <4>1, <4>3, <5>1, <6>1
            DEF Inv, TypeOK, DomainPartitions 
          <6>5. (seq \in PermsOf(seq0))'
            BY <4>1, <4>3, <5>1, Isa
            DEF Inv, TypeOK,  PermsOf 
          <6>6. (UNION UV = 1..Len(seq0))'
            BY  <5>1, <6>1 DEF Inv 
          <6>7. (\A I_1, J \in UV : (I_1 # J) => RelSorted(I_1, J))'
            BY <4>1, <4>3, <5>1, <6>1
            DEF Inv, TypeOK, RelSorted 
          <6>8. QED
            BY <6>2, <6>3, <6>4, <6>5, <6>6, <6>7 DEF Inv          
      <4>4. CASE Cardinality(I) # 1 
        <5>1. seq0' = seq0
          BY DEF a
        <5>I. PICK mn \in 1 .. Len(seq0), mx \in 1 .. Len(seq0) : I = mn .. mx
          BY DEF Inv, UV, DomainPartitions
        <5>mn. mn < mx
          <6>. SUFFICES ASSUME mn >= mx PROVE FALSE 
            OBVIOUS
          <6>1. CASE mn > mx 
            <7>. I = {}
              BY <5>I, <6>1
            <7>. QED  BY DEF Inv, TypeOK
          <6>2. CASE mn = mx
            <7>. I = {mn}
              BY <5>I, <6>2
            <7>. QED  BY <4>4, FS_Singleton
          <6>. QED  BY <6>1, <6>2
        <5> DEFINE I1(p) == mn .. p 
                   I2(p) == (p+1).. mx
        <5>2. PICK p \in mn .. (mx-1) : 
                    /\ seq' \in Partitions(I, p, seq)
                    /\ U' = ((U \ {I}) \cup {I1(p), I2(p)})
          BY <4>2, <4>4, <5>I, <5>mn, IntervalMinMax
        <5>p. mn <= p /\ p < mx
          BY <5>mn
        <5>3. /\ /\ I1(p) # {} 
                 /\ I1(p) \subseteq 1..Len(seq0)
              /\ /\ I2(p) # {} 
                 /\ I2(p) \subseteq 1..Len(seq0)
              /\ I1(p) \cap I2(p) = {}
              /\ I1(p) \cup I2(p) = I
              \* /\ \A i \in I1(p), j \in I2(p) : (i < j) /\ (seq[i] =< seq[j])
          <6>1. mn \in I1(p) /\ mx \in I2(p)
            BY <5>p
          <6>2. /\ I1(p) \subseteq 1 .. Len(seq0)
                /\ I2(p) \subseteq 1 .. Len(seq0)
            BY DEF Inv, TypeOK
          <6>4. I1(p) \cup I2(p) = I
            BY <5>I
          <6>. QED  BY <6>1, <6>2, <6>4
          (*****************************************************************)
          (* Since I is in U, invariant Inv implies I is a non-empty       *)
          (* subinterval of 1..Len(seq), and the <4>4 case assumption      *)
          (* implies Min(I) < Max(I).  Therefore I1(p) and I2(p) are       *)
          (* nonempty subintervals of 1..Len(seq).  It's clear from the    *)
          (* definitions of I1(p) and I2(p) that they are disjoint sets    *)
          (* whose union is I.  The final conjunct follows from the        *)
          (* definition of Partitions(I, p, seq).                          *)
          (*****************************************************************) 
        <5>4. /\ seq' \in Seq(Values)
              /\ Len(seq) = Len(seq')
              /\ Len(seq) = Len(seq0)
          BY <5>2, PermsOfLemma DEF Partitions, Inv, TypeOK
        <5>5. UNION U = UNION U'
          BY <5>2, <5>3
        <5>6. UV' = (UV \ {I}) \cup {I1(p), I2(p)}
          BY <5>1, <5>2, <5>3, <5>4, <5>5 DEF UV
        <5>7. TypeOK'
          <6>1. (seq \in Seq(Values) \ {<<>>})'
            BY <5>4 DEF Inv, TypeOK
          <6>2. (seq0 \in Seq(Values) \ {<<>>})'
            BY <5>1 DEF TypeOK, Inv
          <6>3. (U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} ))'
            BY <5>1, <5>2, <5>3 DEF Inv, TypeOK
          <6>4. (pc \in {"a", "Done"})'
            BY <4>1
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4 DEF TypeOK
        <5>8. ((pc = "Done") => (U = {}))'
          BY <4>1
        <5>9. (UV \in DomainPartitions)'
          \* <6> HIDE DEF I1, I2
          <6>1. UV' \in SUBSET SUBSET (1..Len(seq0'))
            BY <5>6, <5>3, <5>4, <5>1  DEF Inv
          <6>2. UNION UV' = 1..Len(seq0')
            BY <5>6, <5>3, <5>4, <5>1  DEF Inv
          <6>3. ASSUME NEW J \in UV' 
                PROVE  \E i,j \in 1 .. Len(seq0') : J = i .. j
            BY <5>1, <5>mn, <5>6 DEF Inv, TypeOK, DomainPartitions
          <6>4. ASSUME NEW J \in UV', NEW K \in UV', J # K 
                PROVE  J \cap K = {}
            <7>1. CASE J \in UV /\ K \in UV
              BY <6>4, <7>1 DEF Inv, DomainPartitions
            <7>2. CASE J \in (UV \ {I}) /\ K \in {I1(p), I2(p)}
              <8>. J \cap I = {}
                BY <7>2 DEF UV, Inv, DomainPartitions
              <8>. QED  BY <7>2, <5>I
            <7>3. CASE J \in {I1(p), I2(p)} /\ K \in (UV \ {I})
              <8>. K \cap I = {}
                BY <7>3 DEF UV, Inv, DomainPartitions
              <8>. QED  BY <7>3, <5>I
            <7>4. CASE J \in {I1(p), I2(p)} /\ K \in {I1(p), I2(p)}
              BY <6>4, <7>4
            <7>. QED  BY <5>6, <7>1, <7>2, <7>3, <7>4
          <6>5. QED
            BY <6>1, <6>2, <6>3, <6>4 DEF DomainPartitions \*, Min, Max
        <5>10. (seq \in PermsOf(seq0))'
          BY <5>1, <5>2, PermsOfPermsOf DEF Inv, TypeOK, Partitions
        <5>11. (UNION UV = 1..Len(seq0))'
          BY <5>6, <5>3, <5>4, <5>1  DEF Inv
        <5>12. (\A II, JJ \in UV : (II # JJ) => RelSorted(II, JJ))'
          <6> SUFFICES ASSUME NEW II \in UV', NEW JJ \in UV',
                              II # JJ,
                              NEW i \in II, NEW j \in JJ,
                              i < j
                       PROVE  seq'[i] =< seq'[j]
            BY DEF RelSorted
          <6>. /\ i \in 1 .. Len(seq)
               /\ j \in 1 .. Len(seq)
            BY <5>1, <5>4, <5>9 DEF DomainPartitions
          <6>I. /\ I \in SUBSET (1 .. Len(seq))
                /\ p \in I
            BY <5>I, <5>2, PermsOfLemma DEF Inv, TypeOK
          <6>1. CASE II \in UV \ {I} /\ JJ \in UV \ {I}
            BY <5>2, <6>1, Zenon
               DEF Inv, TypeOK, UV, DomainPartitions, Partitions, RelSorted
          <6>2. CASE II \in UV \ {I} /\ JJ \in {I1(p), I2(p)}
            <7>1. JJ \subseteq  I
              BY <5>3, <6>2
            <7>2. PICK k \in I : seq'[j] = seq[k]
              BY <5>2, <7>1, <6>I, PartitionsLemma DEF Inv, TypeOK
            <7>3. II \cap I = {}
              BY <6>2, Zenon DEF UV, Inv, DomainPartitions
            <7>4. PICK mnI, mxI \in 1 .. Len(seq0) : II = mnI .. mxI
              BY <6>2 DEF Inv, DomainPartitions
            <7>5. i < k
              BY <5>I, <6>2, <7>1, <7>3 DEF Inv, TypeOK
            <7>6. seq[i] <= seq[k]
              BY <6>2, <7>1, <7>5 DEF Inv, RelSorted, UV
            <7>7. seq'[i] = seq[i]
              BY <5>2, <6>2, <6>I, <7>3, PartitionsLemma DEF Inv, TypeOK
            <7>. QED  BY <7>2, <7>6, <7>7
          <6>3. CASE II \in {I1(p), I2(p)} /\ JJ \in UV \ {I}
            <7>1. II \subseteq  I
              BY <5>3, <6>3
            <7>2. PICK k \in I : seq'[i] = seq[k]
              BY <5>2, <7>1, <6>I, PartitionsLemma DEF Inv, TypeOK
            <7>3. JJ \cap I = {}
              BY <6>3, Zenon DEF UV, Inv, DomainPartitions
            <7>4. PICK mnJ, mxJ \in 1 .. Len(seq0) : JJ = mnJ .. mxJ
              BY <6>3 DEF Inv, DomainPartitions
            <7>5. k < j
              BY <5>I, <6>3, <7>1, <7>3 DEF Inv, TypeOK
            <7>6. seq[k] <= seq[j]
              BY <6>3, <7>1, <7>5 DEF Inv, RelSorted, UV
            <7>7. seq'[j] = seq[j]
              <8>1. j \in (1 .. Len(seq)) \ I
                BY <7>3
              <8>2. /\ seq \in Seq(Values)
                    /\ seq' \in Partitions(I, p, seq)
                BY <5>2 DEF Inv, TypeOK
              <8>. QED  BY <6>I, <8>1, <8>2, PartitionsLemma
            <7>. QED  BY <7>2, <7>6, <7>7
          <6>4. CASE II = I1(p) /\ JJ = I2(p)
            BY <5>2, <5>3, <6>I, <6>4, PartitionsLemma DEF Inv, TypeOK
          <6>5. CASE II = I2(p) /\ JJ = I2(p)
            BY <6>5  \* contradiction: i < j impossible
          <6> QED  BY <5>6, <6>1, <6>2, <6>3, <6>4, <6>5
        <5>13. QED
          BY <5>7, <5>8, <5>9, <5>10, <5>11, <5>12 DEF Inv
      <4>5. QED
        BY <4>3, <4>4      
    <3>2. CASE U = {}
      <4> USE <3>2 DEF a, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, Min, Max, UV
      <4>1. TypeOK'
        OBVIOUS
      <4>2. ((pc = "Done") => (U = {}))'
        OBVIOUS
      <4>3. (UV \in DomainPartitions)'
        BY Isa
      <4>4. (seq \in PermsOf(seq0))'
        BY Isa
      <4>5. (UNION UV = 1..Len(seq0))'
        OBVIOUS
      <4>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))'
        OBVIOUS
      <4>7. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, Zenon DEF Inv
    <3>3. QED
      BY <3>1, <3>2
  <2>2. CASE UNCHANGED vars
    <3>1. TypeOK'
      BY <2>2 DEF vars, Inv, TypeOK
    <3>2. ((pc = "Done") => (U = {}))'
      BY <2>2 DEF vars, Inv
    <3>3. (UV \in DomainPartitions)'
      BY <2>2, Isa DEF vars, Inv, TypeOK, DomainPartitions, UV
    <3>4. (seq \in PermsOf(seq0))'
      BY <2>2, Isa DEF vars, Inv, TypeOK, DomainPartitions, PermsOf
    <3>5. (UNION UV = 1..Len(seq0))'
      BY <2>2 DEF vars, Inv, UV
    <3>6. (\A I, J \in UV : (I # J) => RelSorted(I, J))'
      BY <2>2 DEF vars, Inv, TypeOK, DomainPartitions, PermsOf, RelSorted, UV
    <3>7. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Inv    
  <2>3. QED
    BY <2>1, <2>2 DEF Next, Terminating
<1>3. Inv => PCorrect
  <2> SUFFICES ASSUME Inv,
                      pc = "Done"
               PROVE  /\ seq \in PermsOf(seq0)
                      /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    BY DEF PCorrect
  <2>1. seq \in PermsOf(seq0)
    BY DEF Inv
  <2>2. \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q]
    <3> SUFFICES ASSUME NEW p \in 1..Len(seq), NEW q \in 1..Len(seq),
                        p < q
                 PROVE  seq[p] =< seq[q]
      OBVIOUS
    <3>1. /\ Len(seq) = Len(seq0)
          /\ Len(seq) \in Nat
          /\ Len(seq) > 0
      BY PermsOfLemma DEF Inv, TypeOK
    <3>2. UV = {{i} : i \in 1..Len(seq)}
      BY U = {} DEF Inv, TypeOK, UV
    <3>3. {p} \in UV /\ {q} \in UV
      BY <3>1, <3>2
    <3> QED
      BY <3>3 DEF Inv, RelSorted
  <2>3. QED
    BY <2>1, <2>2
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================
\* Created Mon Jun 27 08:20:07 PDT 2016 by lamport
