---------------------------- MODULE BinarySearch ----------------------------
(***************************************************************************)
(* This module defines a binary search algorithm for finding an item in a  *)
(* sorted sequence, and contains a TLAPS-checked proof of its safety       *)
(* property.  We assume a sorted sequence seq with elements in some set    *)
(* Values of integers and a number val in Values, it sets the value        *)
(* `result' to either a number i with seq[i] = val, or to 0 if there is no *)
(* such i.                                                                 *)
(*                                                                         *)
(* It is surprisingly difficult to get such a binary search algorithm      *)
(* correct without making errors that have to be caught by debugging.  I   *)
(* suggest trying to write a correct PlusCal binary search algorithm       *)
(* yourself before looking at this one.                                    *)
(*                                                                         *)
(* This algorithm is one of the examples in Section 7.3 of "Proving Safety *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLAPS

CONSTANT Values

ASSUME ValAssump == Values \subseteq Int

SortedSeqs == {ss \in Seq(Values) : 
                 \A i, j \in 1..Len(ss) : (i < j) => (ss[i] =< ss[j])}

(***************************************************************************
--fair algorithm BinarySearch {
   variables seq \in SortedSeqs, val \in Values, 
             low = 1, high = Len(seq), result = 0 ;   
   { a: while (low =< high /\ result = 0) {
          with (mid = (low + high) \div 2, mval = seq[mid]) {
            if (mval = val) { result := mid}
            else if (val < mval) { high := mid - 1}
            else {low := mid + 1}                    } } } }
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

Init == (* Global variables *)
        /\ seq \in SortedSeqs
        /\ val \in Values
        /\ low = 1
        /\ high = Len(seq)
        /\ result = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF low =< high /\ result = 0
           THEN /\ LET mid == (low + high) \div 2 IN
                     LET mval == seq[mid] IN
                       IF mval = val
                          THEN /\ result' = mid
                               /\ UNCHANGED << low, high >>
                          ELSE /\ IF val < mval
                                     THEN /\ high' = mid - 1
                                          /\ low' = low
                                     ELSE /\ low' = mid + 1
                                          /\ high' = high
                               /\ UNCHANGED result
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << low, high, result >>
     /\ UNCHANGED << seq, val >>

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
(* Partial correctness of the algorithm is expressed by invariance of      *)
(* formula resultCorrect.  To get TLC to check this property, we use a     *)
(* model that overrides the definition of Seq so Seq(S) is the set of      *)
(* sequences of elements of S having at most some small length.  For       *)
(* example,                                                                *)
(*                                                                         *)
(*    Seq(S) == UNION {[1..i -> S] : i \in 0..3}                           *)
(*                                                                         *)
(* is the set of such sequences with length at most 3.                     *)
(***************************************************************************)
resultCorrect == 
   (pc = "Done") => IF \E i \in 1..Len(seq) : seq[i] = val
                     THEN seq[result] = val
                     ELSE result = 0 

(***************************************************************************)
(* Proving the invariance of resultCorrect requires finding an inductive   *)
(* invariant that implies it.  A suitable inductive invariant Inv is       *)
(* defined here.  You can use TLC to check that Inv is an inductive        *)
(* invariant.                                                              *)
(***************************************************************************)
TypeOK == /\ seq \in SortedSeqs
          /\ val \in Values
          /\ low \in 1..(Len(seq)+1)
          /\ high  \in 0..Len(seq)
          /\ result \in 0..Len(seq)
          /\ pc \in {"a", "Done"} 
                                   
Inv == /\ TypeOK
       /\ (result /= 0) => (Len(seq) > 0) /\ (seq[result] = val)
       /\ (pc = "a") =>
             IF \E i \in 1..Len(seq) : seq[i] = val 
               THEN \E i \in low..high : seq[i] = val
               ELSE result = 0
       /\ (pc = "Done") => (result /= 0) \/ (\A i \in 1..Len(seq) : seq[i] /= val)

(***************************************************************************)
(* Here is the invariance proof.                                           *)
(***************************************************************************)
THEOREM Spec => []resultCorrect
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. CASE a
    <3>. UNCHANGED <<seq, val>>
      BY <2>1 DEF a
    <3>1. CASE low =< high /\ result = 0
      <4> DEFINE mid == (low + high) \div 2 
                 mval == seq[mid]  
      <4> (low =< mid) /\ (mid =< high) /\ (mid \in 1..Len(seq))
        BY <3>1, Z3 DEF Inv, TypeOK
      <4>1. TypeOK'
        <5>1. seq' \in SortedSeqs
          BY <2>1 DEF a, Inv, TypeOK
        <5>2. val' \in Values
          BY <2>1 DEF a, Inv, TypeOK
        <5>3. (low \in 1..(Len(seq)+1))'
          <6>1. CASE seq[mid] = val 
            BY <6>1, <2>1, <3>1, Z3 DEF Inv, TypeOK, a
          <6>2. CASE seq[mid] /= val 
            BY <6>2, <2>1, <3>1, Z3 DEF Inv, TypeOK, a
          <6>3. QED
            BY <6>1, <6>2
        <5>4. (high  \in 0..Len(seq))'
          <6>1. CASE seq[mid] = val 
            BY <6>1, <2>1, <3>1, Z3 DEF Inv, TypeOK, a
          <6>2. CASE seq[mid] /= val 
            BY <6>2, <2>1, <3>1, Z3 DEF Inv, TypeOK, a
          <6>3. QED
            BY <6>1, <6>2
        <5>5. (result \in 0..Len(seq))'
          <6>1. CASE seq[mid] = val 
            BY <6>1, <2>1, <3>1, Z3 DEF Inv, TypeOK, a
          <6>2. CASE seq[mid] /= val 
            BY <6>2, <2>1, <3>1, Z3 DEF Inv, TypeOK, a
          <6>3. QED
            BY <6>1, <6>2
        <5>6. (pc \in {"a", "Done"})'
          BY <2>1, <3>1 DEF Inv, TypeOK, a
        <5>7. QED
          BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6 DEF TypeOK
      <4>2. ((result /= 0) => (Len(seq) > 0) /\ (seq[result] = val))'
        <5>1. CASE seq[mid] = val 
          BY <5>1, <2>1, <3>1 DEF Inv, TypeOK, a
        <5>2. CASE seq[mid] /= val 
          BY <5>2, <2>1, <3>1 DEF Inv, TypeOK, a
        <5>3. QED
          BY <5>1, <5>2
      <4>3. ((pc = "a") =>
               IF \E i \in 1..Len(seq) : seq[i] = val 
                 THEN \E i \in low..high : seq[i] = val
                 ELSE result = 0)'
        <5>1. CASE seq[mid] = val 
          BY <5>1, <2>1, <3>1 DEF Inv, TypeOK, a
        <5>2. CASE seq[mid] /= val    
          <6>1. /\ (low =< mid) /\ (mid =< high) /\ (mid \in 1..Len(seq))
                /\ Len(seq) > 0 /\ Len(seq) \in Nat
                /\ low \in 1..Len(seq)
                /\ high \in 1..Len(seq)    
            BY ValAssump  DEF Inv, TypeOK
          <6>2. CASE \E i \in 1..Len(seq) : seq[i] = val
            <7>1. PICK i \in low..high : seq[i] = val
             BY <6>2, <2>1 DEF a, Inv
            <7>2. /\ (low =< mid) /\ (mid =< high) /\ (mid \in 1..Len(seq))
                  /\ Len(seq) > 0 /\ Len(seq) \in Nat
                  /\ low \in 1..Len(seq)
                  /\ high \in 1..Len(seq)
                  /\ seq[i] = val
              BY ValAssump, <6>2, <7>1 DEF Inv, TypeOK
            <7>3. \A j \in 1..Len(seq) : seq[j] \in Int
              <8>1. seq \in Seq(Values)
                BY  DEF Inv, TypeOK, SortedSeqs
              <8>2. seq \in Seq(Int)
                BY <8>1, ValAssump
              <8>3. QED
                BY <8>2 DEF Inv, TypeOK, SortedSeqs 
            <7>4. \A j, k \in 1..Len(seq) : j < k => seq[j] =< seq[k]
                BY DEF Inv, TypeOK, SortedSeqs
            <7>5. CASE val < seq[mid]
              <8>1. seq[i] < seq[mid] 
               BY <7>2, <7>5 \*, <8>5 
              <8>2. i < mid
                BY   ValAssump, <7>2, <8>1,  <7>4, <7>3, Z3 
              <8>3. i \in low .. mid-1
                BY ONLY <7>2, <8>1, <8>2, Z3  
              <8>4. /\ (pc' = "a") /\ (low' = low) /\ (high' = mid-1)
                    /\ \E j \in 1..Len(seq) : seq[j] = val
                BY <2>1, <3>1, <5>2, <6>2, <7>5 DEF a, mid
              <8>5. QED
               BY <7>2, <8>4, <8>3 \* , <8>5
            <7>6. CASE ~(val < seq[mid])
              <8> HIDE DEF mid 
              <8>1. seq[mid] < seq[i]
                  BY ValAssump, <7>2, <7>6, <5>2, <7>3, Z3                  
              <8>2. mid < i
                BY   ValAssump, <7>2, <8>1,  (* <8>a,  <9>1, *) <7>3, <7>4, Z3 
              <8>3. i \in mid+1 .. high
                BY <7>2, <8>1, <8>2, Z3  
              <8>4. /\ (pc' = "a") /\ (low' = mid+1) /\ (high' = high)
                    /\ \E j \in 1..Len(seq) : seq[j] = val
                BY <2>1, <3>1, <5>2, <6>2, <7>6 DEF a, mid
              <8>5. QED
               BY <7>2, <8>4, <8>3 \* , <8>5
            <7>7. QED
              BY <7>5, <7>6            
          <6>3. CASE ~ \E i \in 1..Len(seq) : seq[i] = val
            BY <6>3, <5>2, <2>1, <3>1 DEF Inv, TypeOK, a           
          <6>4. QED
            BY <6>2, <6>3  
        <5>3. QED
          BY <5>1, <5>2
      <4>4. ((pc = "Done") => (result /= 0) \/ (\A i \in 1..Len(seq) : seq[i] /= val))'
        BY <3>1, <2>1 DEF Inv, TypeOK,  a
      <4>5. QED
        BY <4>1, <4>2, <4>3, <4>4 DEF Inv
    <3>2. CASE ~(low =< high /\ result = 0)
      BY <3>2, <2>1 DEF Inv, TypeOK,  a      
    <3>3. QED
      BY <3>1, <3>2
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF Inv, TypeOK,  vars
  <2>3. QED
    BY <2>1,  <2>2 DEF Next, Terminating
<1>3. Inv => resultCorrect
   BY  DEF resultCorrect, Inv, TypeOK
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================
\* Modification History
\* Last modified Fri Feb 17 16:12:03 CET 2023 by merz
\* Last modified Tue Aug 27 12:59:52 PDT 2019 by loki
\* Last modified Fri May 03 16:28:58 PDT 2019 by lamport
\* Created Wed Apr 17 15:15:12 PDT 2019 by lamport
