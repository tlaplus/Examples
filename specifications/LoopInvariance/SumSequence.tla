---------------------------- MODULE SumSequence ----------------------------
(***************************************************************************)
(* This module contains a trivial PlusCal algorithm to sum the elements of *)
(* a sequence of integers, together with its non-trivial complete          *)
(* TLAPS-checked proof.                                                    *)
(*                                                                         *)
(* This algorithm is one of the examples in Section 7.3 of "Proving Safety *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, SequenceTheorems, SequencesExtTheorems, NaturalsInduction, TLAPS

(***************************************************************************)
(* To facilitate model checking, we assume that the sequence to be summed  *)
(* consists of integers in a set Values of integers.                       *)
(***************************************************************************)
CONSTANT Values
ASSUME  ValAssump == Values \subseteq Int

(***************************************************************************)
(* In order to be able to express correctness of the algorithm, we define  *)
(* in TLA+ an operator SeqSum so that, if s is the sequence                *)
(*                                                                         *)
(*    s_1, ... , s_n                                                       *)
(*                                                                         *)
(* of integers, then SumSeq(s) equals                                      *)
(*                                                                         *)
(*    s_1 + ... + s_n                                                      *)
(*                                                                         *)
(* The obvious TLA+ definition of SeqSum is                                *)
(*                                                                         *)
(*    RECURSIVE SeqSum(_)                                                  *)
(*    SeqSum(s) == IF s = << >> THEN 0 ELSE s[1] + SeqSum(Tail(s))         *)
(*                                                                         *)
(* However, TLAPS does not yet handle recursive operator definitions, but  *)
(* it does handle recursive function definitions.  So, we define SeqSum in *)
(* terms of a recursively defined function.                                *)
(***************************************************************************)
SeqSum(s) == 
  LET SS[ss \in Seq(Int)] == IF ss = << >> THEN 0 ELSE ss[1] + SS[Tail(ss)]
  IN  SS[s]

(***************************************************************************
Here's the algorithm.  It initially sets seq to an arbitrary sequence
of integers in Values and leaves its value unchanged.  It terminates
with the variable sum equal to the sum of the elements of seq.

--fair algorithm SumSequence {
    variables seq \in Seq(Values), sum = 0, n = 1 ;
    { a: while (n =< Len(seq)) 
          { sum := sum + seq[n] ;
             n := n+1 ;           }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES seq, sum, n, pc

vars == << seq, sum, n, pc >>

Init == (* Global variables *)
        /\ seq \in Seq(Values)
        /\ sum = 0
        /\ n = 1
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF n =< Len(seq)
           THEN /\ sum' = sum + seq[n]
                /\ n' = n+1
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << sum, n >>
     /\ seq' = seq

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness of the algorithm means that it satisfies these two          *)
(* properties:                                                             *)
(*                                                                         *)
(*   - Safety: If it terminates, then it does so with sum equal to         *)
(*             SeqSum(seq).                                                *)
(*                                                                         *)
(*   - Liveness: The algorithm eventually terminates.                      *)
(*                                                                         *)
(* Safety is expressed in TLA+ by the invariance of the following          *)
(* postcondition.                                                          *)
(***************************************************************************)
PCorrect == (pc = "Done") => (sum = SeqSum(seq))

(***************************************************************************)
(* To get TLC to check that the algorithm is correct, we use a model that  *)
(* overrides the definition of Seq so Seq(S) is the set of sequences of    *)
(* elements of S having at most some small length.  For example,           *)
(*                                                                         *)
(*    Seq(S) == UNION {[1..i -> S] : i \in 0..3}                           *)
(*                                                                         *)
(* is the set of such sequences with length at most 3.                     *)
(***************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                           The Proof of Safety                           *)
(*                                                                         *)
(* To prove the invariance of the postcondition, we need to find an        *)
(* inductive invariant that implies it.  A suitable inductive invariant is *)
(* formula Inv defined here.                                               *)
(***************************************************************************)
TypeOK == /\ seq \in Seq(Values)
          /\ sum \in Int
          /\ n \in 1..(Len(seq)+1)
          /\ pc \in {"a", "Done"}
          
Inv == /\ TypeOK
       /\ sum = SeqSum([i \in 1..(n-1) |-> seq[i]])
       /\ (pc = "Done") => (n = Len(seq) + 1) 
       
(***************************************************************************)
(* TLC can check that Inv is an inductive invariant on a large enough      *)
(* model to give us confidence in its correctness.  We can therefore try   *)
(* to use it to prove the postcondition.                                   *)
(***************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* In the course of writing the proof, I found that I needed two simple    *)
(* simple properties of sequences and SeqSum.  The first essentially       *)
(* states that the definition of SeqSum is correct--that is, that it       *)
(* defines the operator we expect it to.  TLA+ doesn't require you to      *)
(* prove anything when making a definition, and it allows you to write     *)
(* silly recursive definitions like                                        *)
(*                                                                         *)
(*    RECURSIVE NotFactorial(_)                                            *)
(*    NotFactorial(i) == IF i = 0 THEN 1 ELSE i * NotFactorial(i+1)        *)
(*                                                                         *)
(* Writing this definition doesn't mean that NonFactorial(4) actually      *)
(* equals 4 * NonFactorial(5).  I think it actually does, but I'm not      *)
(* sure.  I do know that it doesn't imply that NonFactorial(4) is a        *)
(* natural number.  But the recursive definition of SeqSum is sensible,    *)
(* and we can prove the following lemma, which implies that                *)
(* SeqSum(<<1, 2, 3, 4>>) equals 1 + SeqSum(<<2, 3, 4>>).                  *)
(***************************************************************************)
LEMMA Lemma1 ==
        \A s \in Seq(Int) : 
          SeqSum(s) = IF s = << >> THEN 0 ELSE s[1] + SeqSum(Tail(s))

(***************************************************************************)
(* What makes a formal proof of the algorithm non-trivial is that the      *)
(* definition of SeqSum essentially computes SeqSum(seq) by summing the    *)
(* elements of seq from left to right, starting with seq[1].  However, the *)
(* algorithm sums the elements from right to left, starting with           *)
(* seq[Len(s)].  Proving the correctness of the algorithm requires proving *)
(* that the two ways of computing the sum produce the same result.  To     *)
(* state that result, it's convenient to define the operator Front on      *)
(* sequences to be the mirror image of Tail:                               *)
(*                                                                         *)
(*   Front(<<1, 2, 3, 4>>)  =  <<2, 3, 4>>                                 *)
(*                                                                         *)
(* This operator is defined in the SequenceTheorems module.  I find it     *)
(* more convenient to use the slightly different definition expressed by   *)
(* this theorem.                                                           *)
(***************************************************************************)
THEOREM FrontDef  ==  \A S : \A s \in Seq(S) :
                        Front(s) = [i \in 1..(Len(s)-1) |-> s[i]]
BY DEF Front, SubSeq



LEMMA Lemma5  ==  \A s \in Seq(Int) : 
                    (Len(s) > 0) => 
                       (SeqSum(s) =  SeqSum(Front(s)) + s[Len(s)])

(***************************************************************************)
(* If we're interested in correctness of an algorithm, we probably don't   *)
(* want to spend our time proving simple properties of data types.         *)
(* Instead of proving these two obviously correct lemmas, it's best to     *)
(* check them with TLC to make sure we haven't made some silly mistake in  *)
(* writing them, and to prove correctness of the algorithm.  If we want to *)
(* be sure that the lemmas are correct, we can then prove them.  Proofs of *)
(* these lemmas are given below.                                           *)
(***************************************************************************)
-----------------------------------------------------------------------------
THEOREM Spec => []PCorrect
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2>1. TypeOK
    BY Lemma1, ValAssump DEF Init, Inv, TypeOK
  <2>2. sum = SeqSum([i \in 1..(n-1) |-> seq[i]])
    <3>1. (n-1) = 0
      BY DEF Init
    <3>2. [i \in 1..0 |-> seq[i]] = << >>
      OBVIOUS 
    <3>3. << >> \in Seq(Int)
      OBVIOUS
    <3>4. QED
       BY <3>2, <3>1, <3>3, Lemma1 DEF Init
  <2>3. (pc = "Done") => (n = Len(seq) + 1)
    BY Lemma1, ValAssump DEF Init, Inv, TypeOK
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Inv  
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2> USE ValAssump DEF Inv, TypeOK
  <2>1. CASE a
    <3>1. TypeOK'
      <4>1. sum' \in Int
        <5>1. CASE n <= Len(seq)
          <6>. seq[n] \in Values
            BY <5>1
          <6>. QED  BY <5>1, <2>1 DEF a
        <5>2. CASE ~(n <= Len(seq))
          BY <5>2, <2>1 DEF a
        <5>. QED  BY <5>1, <5>2
      <4>. QED  BY <4>1, <2>1 DEF a
    <3>2. (sum = SeqSum([i \in 1..(n-1) |-> seq[i]]))'
      <4>1. CASE n > Len(seq)
        <5> ~(n =< Len(seq))
          BY <4>1 DEF Inv, TypeOK
        <5> QED
         BY <2>1, <4>1 DEF a, Inv, TypeOK
      <4>2. CASE n \in 1..Len(seq)
        <5> DEFINE curseq == [i \in 1..(n-1) |-> seq[i]]
                   s == curseq'
        <5> SUFFICES sum' = SeqSum(s)
          OBVIOUS
        <5>1. /\ n'-1 = n
              /\ Len(s) = n
              /\ s[Len(s)] = seq[n] 
          BY <2>1, <4>2 DEF a, Inv, TypeOK
        <5>2. s = [i \in 1..n |-> seq[i]]
          BY <5>1, <2>1 DEF a
        <5>3. sum' =  sum + seq[n] 
          BY <2>1, <4>2 DEF a
        <5> HIDE DEF s
        <5>4. SeqSum(s) = SeqSum([i \in 1..(Len(s)-1) |-> s[i]]) + s[Len(s)]
          <6>1. \A S, T : S \subseteq T => Seq(S) \subseteq Seq(T)
            OBVIOUS
          <6>2. seq \in Seq(Int)
            BY <6>1, ValAssump DEF Inv, TypeOK
          <6>3. \A i \in 1..n : seq[i] \in Int
            BY <6>2, <4>2
          <6>4. s \in Seq(Int)
            BY <6>3, <5>2, <4>2
          <6>5. Front(s) = [i \in 1 .. Len(s)-1 |-> s[i]]
            BY <5>1 DEF Front
          <6> QED
            BY <6>4, <6>5, <5>1, <4>2, Lemma5 
        <5>5. curseq = [i \in 1..(Len(s)-1) |-> s[i]]
          BY <5>1, <5>2             
        <5>6. sum = SeqSum(curseq)                                 
          BY <2>1, <4>2, <5>5  DEF Inv, TypeOK, s
        <5>7. QED 
          BY <5>1, <5>3, <5>4, <5>5, <5>6 DEF Inv, TypeOK, s 
      <4>3. QED
        BY <4>1, <4>2 DEF Inv, TypeOK
    <3>3. ((pc = "Done") => (n = Len(seq) + 1))'
      BY <2>1 DEF a, Inv, TypeOK
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF Inv
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF Inv, TypeOK, vars
  <2>3. QED
    BY <2>1,  <2>2 DEF Next
<1>3. Inv => PCorrect
  <2> SUFFICES ASSUME Inv,
                      pc = "Done"
               PROVE  sum = SeqSum(seq)
    BY DEF PCorrect
  <2>1. seq = [i \in 1..Len(seq) |-> seq[i]]
    BY DEF Inv, TypeOK
  <2>2. QED
    BY <2>1 DEF Inv, TypeOK  
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(*                          Proofs of the Lemmas.                          *)
(***************************************************************************)

(***************************************************************************)
(* The LET definition at the heart of the definition of SeqSum is a        *)
(* standard definition of a function on sequences by tail recursion.       *)
(* Theorem TailInductiveDef of module SequenceTheorems proves correctness  *)
(* of such a definition.                                                   *)
(***************************************************************************)
LEMMA Lemma1_Proof ==
         \A s \in Seq(Int) : 
          SeqSum(s) = IF s = << >> THEN 0 ELSE s[1] + SeqSum(Tail(s))
<1> DEFINE DefSS(ssOfTailss, ss) == ss[1] + ssOfTailss
           SS[ss \in Seq(Int)] == 
              IF ss = << >> THEN 0 ELSE DefSS(SS[Tail(ss)], ss)         
<1>1. TailInductiveDefHypothesis(SS, Int, 0, DefSS)
  BY DEF TailInductiveDefHypothesis
<1>2. TailInductiveDefConclusion(SS, Int, 0, DefSS) 
  BY <1>1, TailInductiveDef
<1>3. SS = [ss \in Seq(Int) |-> IF ss = << >> THEN 0 
                                              ELSE ss[1] +  SS[Tail(ss)]]
  BY <1>2 DEF TailInductiveDefConclusion
<1> QED 
  BY <1>3 DEF SeqSum

 
(***************************************************************************)
(* Lemmas 2 and 3 are simple properties of Tail and Front that are used in *)
(* the proof of Lemma 5.                                                   *)
(***************************************************************************)
LEMMA Lemma2 == 
       \A S : \A s \in Seq(S) :
          Len(s) > 0 => /\ Tail(s) \in Seq(S)
                        /\ Front(s) \in Seq(S)
                        /\ Len(Tail(s)) = Len(s) - 1
                        /\ Len(Front(s)) = Len(s) - 1
  <1> SUFFICES ASSUME NEW S,
                      NEW s \in Seq(S),
                      Len(s) > 0
               PROVE  /\ Tail(s) \in Seq(S)
                      /\ Front(s) \in Seq(S)
                      /\ Len(Tail(s)) = Len(s) - 1
                      /\ Len(Front(s)) = Len(s) - 1
    OBVIOUS
  <1>1. Tail(s) \in Seq(S) /\ Len(Tail(s)) = Len(s) - 1
    OBVIOUS
  <1>2. Front(s) \in Seq(S) /\ Len(Front(s)) = Len(s) - 1
    BY FrontDef
  <1>3. QED
    BY <1>1, <1>2

LEMMA Lemma2a ==
  ASSUME NEW S, NEW s \in Seq(S), Len(s) > 1
  PROVE  Tail(s) = [i \in 1..(Len(s) - 1) |-> s[i+1]]
<1>. DEFINE t == [i \in 1..(Len(s) - 1) |-> s[i+1]]
<1>1. Tail(s) \in Seq(S) /\ t \in Seq(S)
  OBVIOUS
<1>2. Len(Tail(s)) = Len(t)
  OBVIOUS
<1>3. \A i \in 1 .. Len(Tail(s)) : Tail(s)[i] = t[i]
  OBVIOUS
<1>. QED  BY <1>1, <1>2, <1>3, SeqEqual, Zenon

                   
LEMMA Lemma3 ==
  \A S : \A s \in Seq(S) :
            (Len(s) > 1) => (Tail(Front(s)) = Front(Tail(s)))
  <1> SUFFICES ASSUME NEW S,
                      NEW s \in Seq(S),
                      Len(s) > 1
               PROVE  Tail(Front(s)) = Front(Tail(s))
    OBVIOUS
  <1>1. Tail(Front(s)) = [i \in 1..(Len(s) - 2) |-> s[i+1]]
    <2>1. /\ Front(s) = [i \in 1..(Len(s) - 1) |-> s[i]]
          /\ Len(Front(s)) = Len(s) - 1
          /\ Front(s) \in Seq(S)
          /\ Len(s) \in Nat
      BY FrontDef
    <2>2. Len(Front(s)) > 0
      BY <2>1
     <2>3. Front(s) # << >>
      BY <2>1, <2>2
    <2>4. Tail(Front(s)) = [i \in 1..(Len(Front(s))-1) |-> Front(s)[i+1]]
      BY <2>1, <2>3, Lemma2a
    <2>5. \A i \in 0..(Len(s)-2) : Front(s)[i+1] = s[i+1]
      BY <2>1
    <2>6. Len(Front(s))-1 = Len(s) - 2
      BY <2>1
    <2>7. Tail(Front(s)) = [i \in 1..(Len(s)-2) |-> Front(s)[i+1]]
      BY <2>4, <2>6
    <2>8. \A i \in 1..(Len(s)-2) : Front(s)[i+1] = s[i+1]
      BY <2>5, Z3
    <2>9. QED
      BY <2>7, <2>8
  <1>2. Front(Tail(s)) = [i \in 1..(Len(s) - 2) |-> s[i+1]]
    BY Len(s) \in Nat, Lemma2a DEF Front
  <1>3. QED
    BY <1>1, <1>2


(***************************************************************************)
(* The following lemma asserts type correctness of the SeqSum operator.    *)
(* It's proved by induction on the length of its argument.  Such simple    *)
(* induction is expressed by theorem NatInduction of module                *)
(* NaturalsInduction.                                                      *)
(***************************************************************************)
LEMMA Lemma4 == \A s \in Seq(Int) : SeqSum(s) \in Int
<1> DEFINE P(N) == \A s \in Seq(Int) : (Len(s) = N) => (SeqSum(s) \in Int)
<1>1. P(0)
  <2> SUFFICES ASSUME NEW s \in Seq(Int),
                      Len(s) = 0
               PROVE  SeqSum(s) \in Int
    BY DEF P
  <2>1. s = << >>
    OBVIOUS
  <2> QED
    BY <2>1, Lemma1
<1>2. ASSUME NEW N \in Nat, P(N)
      PROVE  P(N+1)
  <2> SUFFICES ASSUME NEW s \in Seq(Int),
                      Len(s) = (N+1)
               PROVE  SeqSum(s) \in Int
    BY DEF P
  <2>1. s # << >>
    OBVIOUS
  <2>2. SeqSum(s) = s[1] + SeqSum(Tail(s))
    BY <2>1, Lemma1
  <2>3. s[1] \in Int
    BY <2>1
  <2>4. /\ Len(Tail(s)) = N
        /\ Tail(s) \in Seq(Int)
    BY <2>2, Lemma2
  <2>5. SeqSum(Tail(s)) \in Int
    BY <1>2, <2>4
  <2>6. QED
    BY <2>2, <2>3, <2>5
<1> HIDE DEF P
<1>3. \A N \in Nat : P(N)
   BY <1>1, <1>2, NatInduction
<1>4. QED
  BY <1>3 DEF P

  
LEMMA Lemma5_Proof ==
        \A s \in Seq(Int) : 
          (Len(s) > 0) => 
            SeqSum(s) =  SeqSum(Front(s)) + s[Len(s)]
<1> DEFINE P(N) == \A s \in Seq(Int) : 
                     (Len(s) = N) =>  
                        (SeqSum(s) = IF Len(s) = 0
                                      THEN 0
                                      ELSE SeqSum(Front(s)) + s[Len(s)]) 
<1>1. P(0)
  <2> SUFFICES ASSUME NEW s \in Seq(Int),
                      Len(s) = 0
               PROVE  SeqSum(s) = IF Len(s) = 0
                                   THEN 0
                                   ELSE SeqSum(Front(s)) + s[Len(s)]
    BY DEF P
  <2> QED
    BY s = << >>,  Lemma1  
<1>2. ASSUME NEW N \in Nat, P(N)
      PROVE  P(N+1)
  <2> SUFFICES ASSUME NEW s \in Seq(Int),
                      Len(s) = (N+1)
               PROVE  SeqSum(s) = IF Len(s) = 0
                                   THEN 0
                                   ELSE SeqSum(Front(s)) + s[Len(s)]
    BY DEF P
  <2> SUFFICES SeqSum(s) = SeqSum(Front(s)) + s[Len(s)]
    OBVIOUS
  <2>1. /\ Front(s) \in Seq(Int)
        /\ Len(Front(s)) = N
    BY Lemma2, N+1 > 0, (N+1)-1 = N, Zenon
  <2> DEFINE t == Tail(s)
  <2> USE FrontDef 
  <2>2. /\ t \in Seq(Int) 
        /\ Len(t) = N
        /\ SeqSum(s) = s[1] + SeqSum(t)
      BY HeadTailProperties, Lemma1, s # << >>             
  <2>3. CASE N = 0
    <3> USE <2>3
    <3> HIDE FrontDef \* DEF Front
    <3>1. SeqSum(Front(s)) = 0
      BY Lemma1, <2>1, Front(s) = << >>
    <3>2. Len(Tail(s)) = 0
      BY HeadTailProperties
    <3>3. SeqSum(Tail(s)) = 
           IF Tail(s) = << >> THEN 0 ELSE Tail(s)[1] + SeqSum(Tail(Tail(s)))
      BY <2>2, Lemma1
    <3>4. SeqSum(Tail(s)) = 0
      BY <3>2, <2>2, EmptySeq, Tail(s) = << >>, <3>3
    <3>5. QED
      BY <2>2, <3>1, <3>4
  <2>4. CASE N > 0
    <3> /\ Front(s) \in Seq(Int)
        /\ Front(t) \in Seq(Int)
        /\ Tail(Front(s)) \in Seq(Int)
      <4>1. Front(s) \in Seq(Int)
        BY <2>4, <2>2, Lemma2
      <4>2. Front(t) \in Seq(Int)
        BY <2>4, <2>2, Lemma2
      <4>3. Tail(Front(s)) \in Seq(Int)
        <5> Len(s) > 1
          BY <2>4
        <5> Len(Front(s)) > 0
          BY Lemma2
        <5> Front(s) \in Seq(Int)
          BY Lemma2
        <5> Tail(Front(s)) \in Seq(Int)
          BY Lemma2
        <5> QED
          BY Lemma2
      <4>4. QED
        BY <4>1, <4>2, <4>3    
    <3>1. SeqSum(t) = SeqSum(Front(t)) +  t[N]
      BY <1>2, <2>2, <2>4
    <3>2. SeqSum(t) = SeqSum(Tail(Front(s))) + t[N]
      BY <3>1, <2>4, Len(s) > 1, Lemma3 
    <3>3. t[N] = s[N+1]
      BY <2>2, <2>4
    <3> HIDE DEF Front
    <3>4. /\ SeqSum(s) \in Int
          /\ SeqSum(t) \in Int
          /\ SeqSum(Tail(Front(s))) \in Int
          /\ t[N] \in Int
          /\ s[1] \in Int
      <4>1. SeqSum(s) \in Int
        BY <2>4, <2>2, <2>1, Lemma4
      <4>2. SeqSum(t) \in Int
        BY <2>4, <2>2, <2>1, Lemma4
      <4>3. SeqSum(Tail(Front(s))) \in Int
        <5>1. Len(s) > 1
          BY <2>4
        <5>2. Len(Front(s)) > 0
         BY <5>1, FrontDef \* DEF Front
        <5>3. Front(s) # << >>
           BY <5>2
         <5>4. Tail(Front(s)) \in Seq(Int)
           BY <5>3 
         <5>5. QED
        BY <2>4, <2>2, <2>1, <5>3, Lemma4
      <4>4. t[N] \in Int
        BY <2>4, <2>2, <2>1
      <4>4a. s[1] \in Int
         BY <2>4
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4   
    <3>5. SeqSum(s) = s[1] + SeqSum(Tail(Front(s))) + t[N]
      <4>1. SeqSum(s) = s[1] + SeqSum(t)
        BY <2>2
      <4>2. QED
        BY <4>1, <3>2, <3>4, Lemma4, Z3
    <3>6. t[N] = s[N+1]
      BY <2>4
    <3>7. s[1] = Front(s)[1]
      BY <2>4 DEF Front
    <3>8. SeqSum(Front(s)) = Front(s)[1] + SeqSum(Tail(Front(s)))
      BY <2>4, Lemma1
    <3>9. QED
      BY <3>5, <3>6, <3>7, <3>8  
  <2>5. QED
    BY <2>3, <2>4
<1>3. \A N \in Nat : P(N)
  BY <1>1, <1>2, NatInduction
<1>4. QED
  BY <1>3
=============================================================================
\* Modification History
\* Last modified Fri Jan 27 10:03:14 CET 2023 by merz
\* Last modified Tue Aug 27 12:59:10 PDT 2019 by loki
\* Last modified Fri May 03 16:40:42 PDT 2019 by lamport
\* Created Fri Apr 19 14:13:06 PDT 2019 by lamport
