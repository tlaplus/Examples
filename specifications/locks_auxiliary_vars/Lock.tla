--------------------------------- MODULE Lock ---------------------------------

(*****************************************************************************)
(* This module contains the specification of an abstract lock.               *)
(* The proof for mutual exclusion is also detailed.                          *)
(*****************************************************************************)

EXTENDS Integers, TLAPS

(*
--algorithm Lock{
    variables lock = 1;
    
    macro Lock(l){
      await l = 1;
      l := 0;
    }
    
    macro Unlock(l){
      l := 1;
    }
  
    process(proc \in 1..2){
l0:   while(TRUE){
        skip; \* non-critical section
l1:     Lock(lock);
cs:     skip; \* critical section
l2:     Unlock(lock);
      }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "f820ffbb" /\ chksum(tla) = "24b4f3dd")
VARIABLES pc, lock

vars == << pc, lock >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ lock = 1
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ lock' = lock

l1(self) == /\ pc[self] = "l1"
            /\ lock = 1
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ lock' = lock

l2(self) == /\ pc[self] = "l2"
            /\ lock' = 1
            /\ pc' = [pc EXCEPT ![self] = "l0"]

proc(self) == l0(self) \/ l1(self) \/ cs(self) \/ l2(self)

Next == (\E self \in 1..2: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

TypeOK ==
  /\ lock \in {0, 1}
  /\ pc \in [ProcSet -> {"l0", "l1", "cs", "l2"}]

lockcs(i) ==
  pc[i] \in {"cs", "l2"}

LockInv == 
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))
  /\ (\E p \in ProcSet: lockcs(p)) => lock = 0

-------------------------------------------------------------------------------

LEMMA Typing == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY DEF Init, TypeOK
  <1>2. [Next]_vars /\ TypeOK => TypeOK'
    BY DEF TypeOK, vars, Next, proc, l0, l1, cs, l2
  <1>3. QED 
    BY <1>1, <1>2, PTL DEF Spec

THEOREM MutualExclusion == Spec => []LockInv
  <1> USE DEF LockInv, lockcs
  <1>1. Init => LockInv
    BY DEF Init, ProcSet
  <1>2. [Next]_vars /\ TypeOK /\ LockInv => LockInv'
    <2> SUFFICES ASSUME [Next]_vars /\ TypeOK /\ LockInv
                 PROVE LockInv'
      OBVIOUS
    <2>1. ASSUME NEW self \in 1..2, l0(self)
          PROVE LockInv'
      BY <2>1 DEF l0, ProcSet, TypeOK
    <2>2. ASSUME NEW self \in 1..2, l1(self)
          PROVE LockInv'
      BY <2>2 DEF l1, ProcSet, TypeOK
    <2>3. ASSUME NEW self \in 1..2, cs(self)
          PROVE LockInv'
      BY <2>3 DEF cs, ProcSet, TypeOK
    <2>4. ASSUME NEW self \in 1..2, l2(self)
          PROVE LockInv'
      BY <2>4 DEF l2, ProcSet, TypeOK
    <2>5. CASE UNCHANGED vars 
      BY <2>5 DEF vars
    <2>6. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, vars, proc
  <1>3. QED
    BY <1>1, <1>2, Typing, PTL DEF Spec

===============================================================================
