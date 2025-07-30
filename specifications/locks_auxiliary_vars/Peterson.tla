------------------------------- MODULE Peterson -------------------------------

(*****************************************************************************)
(* This module contains the specification for Peterson's Algorithm, taken    *)
(* from the "Parallel Programming" course taught at ULiège.                  *)
(* The invariant `Inv` is the one presented in the course augmented by a     *)
(* clause representing mutual exclusion of the critical section              *)
(* A proof is given to show that `Inv` is inductive.                         *)
(* Moreover the refinement from Peterson to the abstract lock is also proven.*)
(*****************************************************************************)

EXTENDS Integers, TLAPS

Other(p) == IF p = 1 THEN 2 ELSE 1 

(*
--algorithm Peterson{
    variables
      c = [self \in ProcSet |-> FALSE],
      turn = 1;

    process(proc \in 1..2){
a0:   while(TRUE){
        skip;
a1:     c[self] := TRUE;
a2:     turn := Other(self);
a3:     await ~c[Other(self)] \/ turn = self;
cs:     skip;
a4:     c[self] := FALSE;
      }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1d547bc3" /\ chksum(tla) = "8de86c82")
VARIABLES pc, c, turn

vars == << pc, c, turn >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ c = [self \in ProcSet |-> FALSE]
        /\ turn = 1
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << c, turn >>

a1(self) == /\ pc[self] = "a1"
            /\ c' = [c EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ turn' = turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = Other(self)
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ c' = c

a3(self) == /\ pc[self] = "a3"
            /\ ~c[Other(self)] \/ turn = self
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << c, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << c, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ c' = [c EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ turn' = turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3(self) \/ cs(self)
                 \/ a4(self)

Next == (\E self \in 1..2: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

TypeOK ==
  /\ c \in [ProcSet -> BOOLEAN]
  /\ turn \in ProcSet
  /\ pc \in [ProcSet -> {"a0", "a1", "a2", "a3", "cs", "a4"}]

lockcs(i) ==
  pc[i] \in {"cs", "a4"}
Inv ==
  /\ \A p \in ProcSet : c[p] <=> pc[p] \in {"a2", "a3", "cs", "a4"}
  /\ \A p \in ProcSet : pc[p] \in {"cs", "a4"} 
      => (turn = p \/ pc[Other(p)] \in {"a0", "a1", "a2"})
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))

pc_translation(label) ==
  CASE (label = "a0") -> "l0"
    [] (label \in {"a1", "a2", "a3"}) -> "l1"
    [] (label \in {"cs"}) -> "cs"
    [] (label \in {"a4"}) -> "l2"

lock_translation == IF \E p \in ProcSet : pc[p] \in {"cs", "a4"} THEN 0 ELSE 1

L == INSTANCE Lock
     WITH pc <- [p \in ProcSet |-> pc_translation(pc[p])], 
     lock <- lock_translation
LSpec == L!Spec

-------------------------------------------------------------------------------

LEMMA Typing == Spec => []TypeOK
  <1> USE DEF TypeOK
  <1>1. Init => TypeOK
    BY DEF ProcSet, Init
  <1>2. [Next]_vars /\ TypeOK => TypeOK'
    BY DEF ProcSet, Other, Next, vars, proc, a0, a1, a2, a3, cs, a4
  <1>3. QED 
    BY <1>1, <1>2, PTL DEF Spec

THEOREM IndInvariant == Spec => []Inv
  <1> USE DEF Inv, lockcs
  <1>1. Init => Inv
    BY DEF Init
  <1>2. [Next]_vars /\ TypeOK /\ Inv => Inv'
    <2> SUFFICES ASSUME [Next]_vars /\ TypeOK /\ Inv
                 PROVE Inv'
      OBVIOUS
    <2> USE DEF ProcSet, Other
    <2>1. ASSUME NEW self \in 1..2, a0(self)
          PROVE Inv'
      BY <2>1 DEF a0, TypeOK
    <2>2. ASSUME NEW self \in 1..2, a1(self)
          PROVE Inv'
      BY <2>2 DEF a1, TypeOK
    <2>3. ASSUME NEW self \in 1..2, a2(self)
          PROVE Inv'
      BY <2>3 DEF a2, TypeOK
    <2>4. ASSUME NEW self \in 1..2, a3(self)
          PROVE Inv'
      BY <2>4 DEF a3, TypeOK
    <2>5. ASSUME NEW self \in 1..2, cs(self)
          PROVE Inv'
      BY <2>5 DEF cs, TypeOK
    <2>6. ASSUME NEW self \in 1..2, a4(self)
          PROVE Inv'
      BY <2>6 DEF a4, TypeOK
    <2>7. CASE UNCHANGED vars
      BY <2>7 DEF vars
    <2>8. QED 
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF Next, proc
  <1>3. QED
    BY <1>1, <1>2, Typing, PTL DEF Spec

THEOREM Refinement == Spec => L!Spec
  <1> USE DEF pc_translation, lock_translation, ProcSet, L!ProcSet, lockcs
  <1>1. Init => L!Init
    BY DEF Init, L!Init
  <1>2. [Next]_vars /\ TypeOK /\ Inv => [L!Next]_L!vars
    <2> USE DEF L!Next, L!vars, L!proc
    <2> SUFFICES ASSUME [Next]_vars /\ TypeOK /\ Inv
                 PROVE [L!Next]_L!vars
      OBVIOUS
    <2>1. ASSUME NEW self \in 1..2, a0(self)
          PROVE [L!Next]_L!vars
      BY <2>1 DEF a0, L!l0, ProcSet, TypeOK, Inv
    <2>2. ASSUME NEW self \in 1..2, a1(self)
          PROVE [L!Next]_L!vars
      BY <2>2 DEF a1, ProcSet, TypeOK, Inv
    <2>3. ASSUME NEW self \in 1..2, a2(self)
          PROVE [L!Next]_L!vars
      BY <2>3 DEF a2, ProcSet, TypeOK, Inv
    <2>4. ASSUME NEW self \in 1..2, a3(self)
          PROVE [L!Next]_L!vars
      BY <2>4 DEF a3, L!l1, ProcSet, TypeOK, Inv, Other
    <2>5. ASSUME NEW self \in 1..2, cs(self)
          PROVE [L!Next]_L!vars
      BY <2>5 DEF cs, L!cs, ProcSet, TypeOK, Inv
    <2>6. ASSUME NEW self \in 1..2, a4(self)
          PROVE L!l2(self)
      BY <2>6 DEF a4, L!l2, ProcSet, TypeOK, Inv
    <2>7. CASE UNCHANGED vars
      BY <2>7 DEF vars
    <2>8. QED 
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 
      DEF Next, proc, L!Next, L!proc
  <1>3. QED
    BY <1>1, <1>2, Typing, IndInvariant, PTL DEF Spec, L!Spec

===============================================================================
