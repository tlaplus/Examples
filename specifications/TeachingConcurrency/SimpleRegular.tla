--------------------------- MODULE SimpleRegular ---------------------------
(***************************************************************************)
(* This is a minor modification of the algorithm in module Simple.  That   *)
(* algorithm is an N-process algorithm shared-memory algorithm, in which   *)
(* each process i has a shared register x[i] that it writes and is read by *)
(* process x[(i-1) % N].  Each process i also has a local register y[i]    *)
(* that only it can access.                                                *)
(*                                                                         *)
(* The shared registers x[i] in the algorithm of module Simple are assumed *)
(* to be atomic, effectively meaning that each read or write by any        *)
(* process is an atomic action.  In the algorithm in this module, the x[i] *)
(* are assumed to be a weaker class of registers called regular registers. *)
(* Atomic and regular registers are defined in the paper                   *)
(*                                                                         *)
(*    On Interprocess Communication                                        *)
(*    Distributed Computing 1, 2 (1986), 77-101                            *)
(*                                                                         *)
(* which can be found on the Web at                                        *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/pubs/interprocess.pdf               *)
(*                                                                         *)
(* That paper considers only registers that can be written by a single     *)
(* process, but takes into account that reads and writes are not           *)
(* instantaneous atomic actions, but take a finite length of time and can  *)
(* overlap.  An atomic register is one in which a read and write acts as   *)
(* if it were executed atomically at some time between the beginning and   *)
(* end of the operation.  An atomic register can be modeled as one in      *)
(* which each read and write is a single step in an execution.             *)
(*                                                                         *)
(* A regular register is defined there to be one in which a read that      *)
(* overlaps some (possibly empty) set of writes to a register obtains a    *)
(* value that is either the register's value before any of the writes were *)
(* begun or one of the values being written by one of the writes that the  *)
(* read overlaps.  (Hence, a read that overlaps no writes obtains the last *)
(* value written before the read, or the initial value if there were no    *)
(* such writes before the read.) A regular register r can be modeled in a  *)
(* TLA+ spec modeled as a variable rv that equals a set of values.  The    *)
(* register having a value v is modeled by rv equaling {v}.  When a value  *)
(* w different from v is written to r, the value of rv first changes to    *)
(* {v, w} and then to {w}.  A read of r is modeled as an atomic step that  *)
(* can obtain any value in the set rv.                                     *)
(*                                                                         *)
(* The algorithm of this model is obtained from that of module Simple by   *)
(* letting each value x[i] be the set of values representing a regular     *)
(* register.  Since each y[i] is local to process i, we can consider it to *)
(* be atomic.                                                              *)
(*                                                                         *)
(* The problem of generalizing the algorithm of module Simple to use       *)
(* regular registers was proposed by Yuri Abraham in                       *)
(*                                                                         *)
(*    On Lamport's "Teaching Concurrency"                                  *)
(*    Bulletin of EATS (European Association for Theoretical Computer      *)
(*      Science) No. 127, February 2019                                    *)
(*    http://bulletin.eatcs.org/index.php/beatcs/article/view/569          *)
(***************************************************************************)
EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NAssump ==  (N \in Nat) /\ (N > 0)

(***************************************************************************
--algorithm SimpleRegular {
    variables x = [i \in 0..(N-1) |-> {0}], y = [i \in 0..(N-1) |-> 0] ;
    process (proc \in 0..N-1) {
      a1: x[self] := {0,1} ;
      a2: x[self] := {1} ;
      b:  with (v \in x[(self-1) % N]) {y[self] := v }
    }
}
****************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0..N-1)

Init == (* Global variables *)
        /\ x = [i \in 0..(N-1) |-> {0}]
        /\ y = [i \in 0..(N-1) |-> 0]
        /\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ x' = [x EXCEPT ![self] = {0,1}]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ y' = y

a2(self) == /\ pc[self] = "a2"
            /\ x' = [x EXCEPT ![self] = {1}]
            /\ pc' = [pc EXCEPT ![self] = "b"]
            /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ \E v \in x[(self-1) % N]:
                y' = [y EXCEPT ![self] = v]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a1(self) \/ a2(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..N-1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* The definition of PCorrect is the same as in module Simple.             *)
(***************************************************************************)
PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") => 
                (\E i \in 0..(N-1) : y[i] = 1)

(***************************************************************************)
(* The type invariant TypeOK is the obvious modification of the type       *)
(* invariant TypeOK of module Simple.  Except for the change to the        *)
(* definition of TypeOK, the inductive invariant Inv is the same as in     *)
(* module Simple.                                                          *)
(***************************************************************************)
TypeOK == /\ x \in [0..(N-1) -> (SUBSET {0, 1}) \ {{}}]
          /\ y \in [0..(N-1) -> {0,1}]
          /\ pc \in [0..(N-1) -> {"a1", "a2", "b", "Done"}]
                    
Inv ==  /\ TypeOK
        /\ \A i \in 0..(N-1) : (pc[i] \in {"b", "Done"}) => (x[i] = {1})
        /\ \/ \E i \in 0..(N-1) : pc[i] /= "Done"
           \/ \E i \in 0..(N-1) : y[i] = 1

(***************************************************************************)
(* The proof of invariance of PCorrect differs from the proof in module    *)
(* Simple only because the single action a has been replaced by the two    *)
(* actions a1 and a2, and because the proof that b maintains the truth of  *)
(* the invariant required one extra decomposition to allow Z3 to prove it. *)
(* As before, the decomposition of the proof of <1>2 was essentially       *)
(* generated with the Toolbox's Decompose Proof command.                   *)
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
  <2>1. ASSUME NEW self \in 0..N-1,
               a1(self)
        PROVE  Inv'
    BY <2>1 DEF a1, Inv, TypeOK
  <2>2. ASSUME NEW self \in 0..N-1,
               a2(self)
        PROVE  Inv'
    BY <2>2 DEF a2, Inv, TypeOK
  <2>3. ASSUME NEW self \in 0..N-1,
               b(self)
        PROVE  Inv'
    <3> SUFFICES ASSUME NEW v \in x[(self-1) % N],
                        y' = [y EXCEPT ![self] = v]
                 PROVE  Inv'
      BY <2>3 DEF b
    <3> QED
        BY <2>3, Z3 DEF b, Inv, TypeOK  
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF TypeOK, Inv, vars
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4 DEF Next, Terminating, proc
<1>3. Inv => PCorrect
  BY DEF Inv, TypeOK, PCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
======================================       
\* Modification History
\* Last modified Tue May 14 07:18:15 PDT 2019 by lamport
\* Created Mon Apr 15 16:25:14 PDT 2019 by lamport
