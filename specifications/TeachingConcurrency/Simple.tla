------------------------------ MODULE Simple ------------------------------
(***************************************************************************)
(* This is a trivial example from the document "Teaching Conccurrency"     *)
(* that appeared in                                                        *)
(*                                                                         *)
(*     ACM SIGACT News Volume 40, Issue 1 (March 2009), 58-62              *)
(*                                                                         *)
(* A copy of that article is at                                            *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/pubs/teaching-concurrency.pdf       *)
(*                                                                         *)
(* It is also the example in Section 7.2 of "Proving Safety Properties",   *)
(* which is at                                                             *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NAssump ==  (N \in Nat) /\ (N > 0)

(****************************************************************************
Here is the algorithm in PlusCal.  It's easy to understand if you think
of the N processes, numbered from 0 through N-1, as arranged in a
circle, with processes (i-1) % N and (i+1) % N being the processes on
either side of process i.

--algorithm Simple {
    variables x = [i \in 0..(N-1) |-> 0], y = [i \in 0..(N-1) |-> 0] ;
    process (proc \in 0..N-1) {
      a: x[self] := 1 ;
      b: y[self] := x[(self-1) % N]
    }
}
****************************************************************************)
\* BEGIN TRANSLATION  This is the TLA+ translation of the PlusCal code.
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0..N-1)

Init == (* Global variables *)
        /\ x = [i \in 0..(N-1) |-> 0]
        /\ y = [i \in 0..(N-1) |-> 0]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ x' = [x EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ y' = [y EXCEPT ![self] = x[(self-1) % N]]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
----------------------------------------------------------------------------
(***************************************************************************)
(* The property of this algorithm we want to prove is that, when all the   *)
(* processes have terminated, y[i] equals 1 for at least one process i.   *)
(* This property is express by the invariance of the following formula     *)
(* PCorrect.  In other words, we have to prove the theorem                 *)
(*                                                                         *)
(*    Spec => []PCorrect                                                   *)
(***************************************************************************)
PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") => 
                (\E i \in 0..(N-1) : y[i] = 1)

(***************************************************************************)
(* Proving the invariance of PCorrect requires finding an inductive        *)
(* invariant Inv that implies it.  As usual, the inductive invariant       *)
(* includes a type-correctness invariant, which is the following formula   *)
(* TypeOK.                                                                 *)
(***************************************************************************)
TypeOK == /\ x \in [0..(N-1) -> {0,1}]
          /\ y \in [0..(N-1) -> {0,1}]
          /\ pc \in [0..(N-1) -> {"a", "b", "Done"}]
 
(***************************************************************************)
(* It's easy to use TLC to check that the following formula Inv is an      *)
(* inductive invariant of the algorithm.  You should also be able check    *)
(* that the propositional logic tautology                                  *)
(*                                                                         *)
(*    (A => B) = ((~A) \/ B)                                               *)
(*                                                                         *)
(* and the predicate logic tautology                                       *)
(*                                                                         *)
(*    (~ \A i \in S : P(i))  =  \E i \in S : ~P(i)                         *)
(*                                                                         *)
(* imply that the last conjunct of Inv is equivalet to PCorrect.  When I   *)
(* wrote the definition, I knew that this conjunct of Inv implied          *)
(* PCorrect, but I didn't realize that the two were equivalent until I saw *)
(* the invariant written in terms of PCorrect in a paper by Yuri Abraham.  *)
(* That's why I originally didn't define Inv in terms of PCorrect.  I'm    *)
(* not sure why, but I find the implication to be a more natural way to    *)
(* write the postcondition PCorrect and the disjunction to be a more       *)
(* natural way to think about the inductive invariant.                     *)
(***************************************************************************)                   
Inv ==  /\ TypeOK
        /\ \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = 1)
        /\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1


(***************************************************************************)
(* Here is the proof of correctness.  The top-level steps <1>1 - <1>4 are  *)
(* the standard ones for an invariance proof, and the decomposition of the *)
(* proof of <1>2 was done with the Toolbox's Decompose Proof command.  It  *)
(* was trivial to get TLAPS to check the proof, except for the proof of    *)
(* <2>2.  A comment explains the problem I had with that step.             *)
(***************************************************************************)
THEOREM Spec => []PCorrect
<1> USE NAssump
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, ProcSet 
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self \in 0..(N-1),
               a(self)
        PROVE  Inv'
    BY <2>1 DEF a, Inv, TypeOK
  <2>2. ASSUME NEW self \in 0..(N-1),
               b(self)
        PROVE  Inv'
    (***********************************************************************)
    (* I spent a lot of time decomposing this step down to about level <5> *)
    (* until I realized that the problem was that the default SMT solver   *)
    (* in the version of TLAPS I was using was CVC3, which seems to know   *)
    (* nothing about the % operator.  When I used Z3, no further           *)
    (* decomposition was needed.                                           *)
    (***********************************************************************)
    BY <2>2, Z3 DEF b, Inv, TypeOK
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF TypeOK, Inv, vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next, Terminating, proc
<1>3. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
=============================================================================
\* Modification History
\* Last modified Wed May 15 02:33:18 PDT 2019 by lamport
\* Created Mon Apr 15 16:25:14 PDT 2019 by lamport
