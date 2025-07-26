------------------------------- MODULE Barriers -------------------------------

EXTENDS TLAPS, Integers, FiniteSets, FiniteSetTheorems

CONSTANTS
  N

(**
--algorithm Barrier {
    variables
      lock = 1,
      gate_1 = 0,
      gate_2 = 0,
      rdv = 0;

    macro Lock(l) {
        await l = 1;
        l := 0;
    }

    macro Unlock(l) {
        l := 1;
    }

    macro Wait(s) {
        await s > 0;
        s := s - 1;
    }

    macro Signal(s) {
        s := s + N;
    }

    process (proc \in 1..N) {
a0:   while (TRUE) {
        skip; \* Some code
a1:     Lock(lock);
a2:     rdv := rdv + 1;
a3:     if (rdv = N) {
a4:       Signal(gate_1);
        };
a5:     Unlock(lock);
a6:     Wait(gate_1);
a7:     Lock(lock);
a8:     rdv := rdv - 1;
a9:     if (rdv = 0) {
a10:      Signal(gate_2);
        };
a11:    Unlock(lock);
a12:    Wait(gate_2);
      }
    }
}
**)
\* BEGIN TRANSLATION (chksum(pcal) = "fa4cafb2" /\ chksum(tla) = "4cd2e9fd")
VARIABLES pc, lock, gate_1, gate_2, rdv

vars == << pc, lock, gate_1, gate_2, rdv >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ lock = 1
        /\ gate_1 = 0
        /\ gate_2 = 0
        /\ rdv = 0
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << lock, gate_1, gate_2, rdv >>

a1(self) == /\ pc[self] = "a1"
            /\ lock = 1
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << gate_1, gate_2, rdv >>

a2(self) == /\ pc[self] = "a2"
            /\ rdv' = rdv + 1
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ UNCHANGED << lock, gate_1, gate_2 >>

a3(self) == /\ pc[self] = "a3"
            /\ IF rdv = N
                  THEN /\ pc' = [pc EXCEPT ![self] = "a4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << lock, gate_1, gate_2, rdv >>

a4(self) == /\ pc[self] = "a4"
            /\ gate_1' = gate_1 + N
            /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << lock, gate_2, rdv >>

a5(self) == /\ pc[self] = "a5"
            /\ lock' = 1
            /\ pc' = [pc EXCEPT ![self] = "a6"]
            /\ UNCHANGED << gate_1, gate_2, rdv >>

a6(self) == /\ pc[self] = "a6"
            /\ gate_1 > 0
            /\ gate_1' = gate_1 - 1
            /\ pc' = [pc EXCEPT ![self] = "a7"]
            /\ UNCHANGED << lock, gate_2, rdv >>

a7(self) == /\ pc[self] = "a7"
            /\ lock = 1
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "a8"]
            /\ UNCHANGED << gate_1, gate_2, rdv >>

a8(self) == /\ pc[self] = "a8"
            /\ rdv' = rdv - 1
            /\ pc' = [pc EXCEPT ![self] = "a9"]
            /\ UNCHANGED << lock, gate_1, gate_2 >>

a9(self) == /\ pc[self] = "a9"
            /\ IF rdv = 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "a10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "a11"]
            /\ UNCHANGED << lock, gate_1, gate_2, rdv >>

a10(self) == /\ pc[self] = "a10"
             /\ gate_2' = gate_2 + N
             /\ pc' = [pc EXCEPT ![self] = "a11"]
             /\ UNCHANGED << lock, gate_1, rdv >>

a11(self) == /\ pc[self] = "a11"
             /\ lock' = 1
             /\ pc' = [pc EXCEPT ![self] = "a12"]
             /\ UNCHANGED << gate_1, gate_2, rdv >>

a12(self) == /\ pc[self] = "a12"
             /\ gate_2 > 0
             /\ gate_2' = gate_2 - 1
             /\ pc' = [pc EXCEPT ![self] = "a0"]
             /\ UNCHANGED << lock, gate_1, rdv >>

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3(self) \/ a4(self)
                 \/ a5(self) \/ a6(self) \/ a7(self) \/ a8(self)
                 \/ a9(self) \/ a10(self) \/ a11(self) \/ a12(self)

Next == (\E self \in 1..N: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

-------------------------------------------------------------------------------

TypeOK ==
  /\ lock \in {0, 1}
  /\ gate_1 \in Nat
  /\ gate_2 \in Nat
  /\ rdv \in Int
  /\ pc \in [ProcSet -> {"a0", "a1", "a2", "a3", "a4", "a5", "a6", 
            "a7", "a8", "a9", "a10", "a11", "a12"}]

lockcs(p) ==
  pc[p] \in {"a2", "a3", "a4", "a5", "a8", "a9", "a10", "a11"}
ProcsInLockCS ==
  {p \in ProcSet: lockcs(p)}

LockInv == 
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))
  /\ (\E p \in ProcSet: lockcs(p)) => lock = 0
  
rdvsection(p) ==
  pc[p] \in {"a3", "a4", "a5", "a6", "a7", "a8"}
ProcsInRdv ==
  {p \in ProcSet : rdvsection(p)}
  
barrier1(p) ==
  pc[p] \in {"a0", "a1", "a2", "a3", "a4", "a5", "a6"}
ProcsInB1 ==
  {p \in ProcSet : barrier1(p)}
  
barrier2(p) ==
  pc[p] \in {"a7", "a8", "a9", "a10", "a11", "a12"}
ProcsInB2 ==
  {p \in ProcSet : barrier2(p)}

Inv == 
  \* the semaphore values are kept between 0 and N
  /\ gate_1 \in 0..N
  /\ gate_2 \in 0..N
  \* rdv is the amount of processes in ]a2 ; a8]
  /\ rdv = Cardinality(ProcsInRdv) \* proves that rdv \in 0..N
  \* open gates mean that at least one process must be in the correct 
  \* waiting section
  /\ gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"}
  /\ gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"}
  \* at least one gate must be closed
  /\ (gate_1 = 0) \/ (gate_2 = 0)
  \* if one process in the first barrier (or about to enter), 
  \* then second barrier must be empty
  /\ (\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
      => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
  \* if one process in second barrier, then first barrier must be empty
  /\ (\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
      => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
  \* The value of gate_1 is bounded by the count of processes 
  \* in the first barrier
  /\ gate_1 =< Cardinality(ProcsInB1)
  \* if one process arrives at the first barrier, the first gate is locked
  /\ (\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
      => gate_1 = 0
  \* if one process is in a4, that means rdv is equal to N and 
  \* all other processes are waiting on gate_1
  /\ \A p \in ProcSet: pc[p] = "a4" => (
          /\ rdv = N
          /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
     )
  \* The value of gate_2 is bounded by the count of processes 
  \* in the second barrier
  /\ gate_2 =< Cardinality(ProcsInB2)
  \* if one process arrives at the second barrier, the second gate is locked
  /\ (\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
      => gate_2 = 0
  \* if one process is in a10, that means rdv is equal to 0 and 
  \* all other processes are waiting on gate_2
  /\ \A p \in ProcSet: pc[p] = "a10" => (
          /\ rdv = 0
          /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
     )

FlushInv ==
  /\ gate_1 > 0 => gate_1 = Cardinality(ProcsInB1)
  /\ gate_2 > 0 => gate_2 = Cardinality(ProcsInB2)

pc_translation(self) ==
  IF pc[self] \in {"a1", "a2", "a3", "a4", "a5", "a6", "a7", "a8", "a9", "a10"}
    THEN "b1"
  ELSE IF pc[self] = "a0" 
    THEN "b0"
  ELSE IF gate_2 > 0
    THEN "b0"
  ELSE "b1"

B == INSTANCE Barrier WITH pc <- [p \in ProcSet |-> pc_translation(p)]

-------------------------------------------------------------------------------

ASSUME N_Assumption == N \in Nat \ {0} 

LEMMA Typing == Spec => []TypeOK
  <1> USE N_Assumption DEF TypeOK
  <1>1. Init => TypeOK
    BY DEF Init
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    BY DEF Next, proc, vars, 
           a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

LEMMA LockExclusion == Spec => []LockInv
  <1> USE DEF LockInv, lockcs, TypeOK
  <1>1. Init => LockInv 
    BY DEF Init
  <1>2. LockInv /\ TypeOK /\ [Next]_vars => LockInv'
    <2> SUFFICES ASSUME LockInv /\ TypeOK /\ [Next]_vars
                 PROVE  LockInv'
      OBVIOUS
    <2>1. ASSUME NEW self \in 1..N, a0(self)
        PROVE LockInv'
      BY <2>1 DEF a0
    <2>2. ASSUME NEW self \in 1..N, a1(self)
        PROVE LockInv'
      BY <2>2 DEF a1
    <2>3. ASSUME NEW self \in 1..N, a2(self)
        PROVE LockInv'
      BY <2>3 DEF a2
    <2>4. ASSUME NEW self \in 1..N, a3(self)
        PROVE LockInv'
      BY <2>4 DEF a3
    <2>5. ASSUME NEW self \in 1..N, a4(self)
        PROVE LockInv'
      BY <2>5 DEF a4
    <2>6. ASSUME NEW self \in 1..N, a5(self)
        PROVE LockInv'
      BY <2>6 DEF a5, ProcSet
    <2>7. ASSUME NEW self \in 1..N, a6(self)
        PROVE LockInv'
      BY <2>7 DEF a6
    <2>8. ASSUME NEW self \in 1..N, a7(self)
        PROVE LockInv'
      BY <2>8 DEF a7
    <2>9. ASSUME NEW self \in 1..N, a8(self)
        PROVE LockInv'
      BY <2>9 DEF a8
    <2>10. ASSUME NEW self \in 1..N, a9(self)
        PROVE LockInv'
      BY <2>10 DEF a9
    <2>11. ASSUME NEW self \in 1..N, a10(self)
        PROVE LockInv'
      BY <2>11 DEF a10
    <2>12. ASSUME NEW self \in 1..N, a11(self)
        PROVE LockInv'
      BY <2>12 DEF a11, ProcSet
    <2>13. ASSUME NEW self \in 1..N, a12(self)
        PROVE LockInv'
      BY <2>13 DEF a12
    <2>14. CASE UNCHANGED vars
        BY <2>14 DEF vars
    <2>15. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, 
         <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14
      DEF Next, proc, ProcSet
  <1>3. QED
    BY <1>1, <1>2, PTL, Typing DEF Spec

LEMMA ProcSetSubSetsBound ==
    /\ IsFiniteSet(ProcsInRdv) /\ Cardinality(ProcsInRdv) \in 0..N
    /\ IsFiniteSet(ProcsInB1) /\ Cardinality(ProcsInB1) \in 0..N
    /\ IsFiniteSet(ProcsInB1)' /\ Cardinality(ProcsInB1)' \in 0..N
    /\ IsFiniteSet(ProcsInB2) /\ Cardinality(ProcsInB2) \in 0..N
    /\ IsFiniteSet(ProcsInB2)' /\ Cardinality(ProcsInB2)' \in 0..N
  <1> USE N_Assumption
  <1>1. /\ ProcsInRdv \subseteq ProcSet
        /\ ProcsInB1 \subseteq ProcSet
        /\ ProcsInB1' \subseteq ProcSet
        /\ ProcsInB2 \subseteq ProcSet
        /\ ProcsInB2' \subseteq ProcSet
    BY DEF ProcSet, ProcsInRdv, ProcsInB1, ProcsInB2
  <1>2. /\ IsFiniteSet(ProcSet)
        /\ Cardinality(ProcSet) = N
    BY FS_Interval DEF ProcSet
  <1>3. /\ IsFiniteSet(ProcsInRdv) /\ Cardinality(ProcsInRdv) <= N
        /\ IsFiniteSet(ProcsInB1) /\ Cardinality(ProcsInB1) <= N
        /\ IsFiniteSet(ProcsInB1)' /\ Cardinality(ProcsInB1)' <= N
        /\ IsFiniteSet(ProcsInB2) /\ Cardinality(ProcsInB2) <= N
        /\ IsFiniteSet(ProcsInB2)' /\ Cardinality(ProcsInB2)' <= N
    BY FS_Subset, <1>1, <1>2
  <1>4. /\ Cardinality(ProcsInRdv) \in 0..N
        /\ Cardinality(ProcsInB1) \in 0..N
        /\ Cardinality(ProcsInB1)' \in 0..N
        /\ Cardinality(ProcsInB2) \in 0..N
        /\ Cardinality(ProcsInB2)' \in 0..N
    BY <1>3, FS_CardinalityType
  <1>5. QED
    BY <1>3, <1>4
    
LEMMA AllProcsInRdv == 
    (Cardinality(ProcsInRdv) = N) => (\A p \in ProcSet : rdvsection(p)) 
  <1> USE N_Assumption
  <1>1. ProcsInRdv \subseteq ProcSet
    BY DEF ProcSet, ProcsInRdv
  <1>2. /\ IsFiniteSet(ProcSet)
        /\ Cardinality(ProcSet) = N
    BY FS_Interval DEF ProcSet
  <1>3. (Cardinality(ProcsInRdv) = N) => ProcsInRdv = ProcSet
    BY <1>1, <1>2, FS_Subset
  <1>4. (Cardinality(ProcsInRdv) = N) => (\A p \in ProcSet : rdvsection(p))
    BY <1>3 DEF ProcsInRdv
  <1>5. QED
    BY <1>4
    
LEMMA AllProcsNotInRdv ==
    (Cardinality(ProcsInRdv) = 0) => ~(\E p \in ProcSet : rdvsection(p))
  <1> USE N_Assumption
  <1>1. IsFiniteSet(ProcsInRdv)
    BY ProcSetSubSetsBound, PTL
  <1>2. (Cardinality(ProcsInRdv) = 0) => (ProcsInRdv = {})
    BY <1>1, FS_EmptySet
  <1>3. (Cardinality(ProcsInRdv) = 0) => ~(\E p \in ProcSet : rdvsection(p))
    BY <1>2 DEF ProcsInRdv
  <1>4. QED
    BY <1>3

THEOREM FS_NonEmptySet ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE Cardinality(S) > 0 <=> \E x: x \in S
    BY FS_EmptySet, FS_CardinalityType
    
THEOREM FS_TwoElements ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE Cardinality(S) > 1 => \E x, y \in S: x # y
  <1> SUFFICES ASSUME Cardinality(S) > 1
               PROVE \E x, y \in S: x # y
    OBVIOUS
  <1>1. PICK x : x \in S
    <2>1. Cardinality(S) > 0
      BY FS_CardinalityType
    <2>2. QED
      BY <2>1, FS_NonEmptySet
  <1>2. PICK y : x # y /\ y \in S
    <2> DEFINE T == S \ {x}
    <2>1. /\ IsFiniteSet(T)
          /\ Cardinality(T) = Cardinality(S) - 1
      BY <1>1, FS_RemoveElement
    <2>2. Cardinality(T) > 0
      BY <2>1, FS_CardinalityType
    <2>3. \E y : y \in T
      BY <2>1, <2>2, FS_NonEmptySet
    <2>4. QED
      BY <2>3
  <1>3. QED
    BY <1>1, <1>2

THEOREM Invariant == Spec => []Inv
  <1> USE N_Assumption 
      DEF Inv, lockcs, rdvsection, ProcsInRdv, 
          barrier1, ProcsInB1, barrier2, ProcsInB2
  <1>1. Init => Inv
    <2> SUFFICES ASSUME Init
                 PROVE  Inv
      OBVIOUS
    <2>1. gate_1 \in 0..N
      BY DEF Init
    <2>2. gate_2 \in 0..N
      BY DEF Init
    <2>3. rdv = Cardinality(ProcsInRdv)
      BY FS_EmptySet DEF Init
    <2>4. gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"}
      BY DEF Init
    <2>5. gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"}
      BY DEF Init
    <2>6. (gate_1 = 0) \/ (gate_2 = 0)
      BY DEF Init
    <2>7. (\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
           => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
      BY DEF Init
    <2>8. (\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
           => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
      BY DEF Init
    <2>9. gate_1 =< Cardinality(ProcsInB1)
      BY FS_Subset, FS_Interval DEF Init, ProcSet
    <2>10. (\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
            => gate_1 = 0
      BY DEF Init
    <2>11. \A p \in ProcSet: pc[p] = "a4" => (
                /\ rdv = N
                /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
           )
      BY DEF Init
    <2>12. gate_2 =< Cardinality(ProcsInB2)
      BY FS_EmptySet DEF Init
    <2>13. (\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
            => gate_2 = 0
      BY DEF Init
    <2>14. \A p \in ProcSet: pc[p] = "a10" => (
                /\ rdv = 0
                /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
           )
      BY DEF Init
    <2>15. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, 
         <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14
  <1>2. Inv /\ TypeOK /\ LockInv /\ [Next]_vars => Inv'
    <2> SUFFICES ASSUME Inv,
                        TypeOK,
                        LockInv,
                        [Next]_vars
                 PROVE  Inv'
      OBVIOUS
    <2>1. ASSUME NEW self \in 1..N,
                 a0(self)
          PROVE  Inv'
      BY <2>1 DEF a0, TypeOK
    <2>2. ASSUME NEW self \in 1..N,
                 a1(self)
          PROVE  Inv'
      BY <2>2 DEF a1, TypeOK, LockInv
    <2>3. ASSUME NEW self \in 1..N,
                 a2(self)
          PROVE  Inv'
      <3>1. (gate_1 \in 0..N)'
        BY <2>3 DEF a2
      <3>2. (gate_2 \in 0..N)'
        BY <2>3 DEF a2
      <3>3. (rdv = Cardinality(ProcsInRdv))'
        <4>1. /\ ProcsInRdv \union {self} = ProcsInRdv' 
              /\ self \notin ProcsInRdv
          BY <2>3 DEF a2, ProcSet, TypeOK
        <4> HIDE DEF ProcsInRdv
        <4>2. /\ IsFiniteSet(ProcsInRdv')
              /\ Cardinality(ProcsInRdv') = Cardinality(ProcsInRdv) + 1
          BY <4>1, FS_AddElement, ProcSetSubSetsBound
        <4>3. (rdv = Cardinality(ProcsInRdv))'
          BY <2>3, <4>2 DEF a2
        <4>4. QED
          BY <4>3
      <3>4. (gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"})'
        BY <2>3 DEF a2, TypeOK
      <3>5. (gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"})'
        BY <2>3 DEF a2, TypeOK
      <3>6. ((gate_1 = 0) \/ (gate_2 = 0))'
        BY <2>3 DEF a2
      <3>7. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
              => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"}))'
        BY <2>3 DEF a2, TypeOK
      <3>8. ((\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
              => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"}))'
        BY <2>3 DEF a2, TypeOK
      <3>9. (gate_1 =< Cardinality(ProcsInB1))'
        BY <2>3 DEF a2, TypeOK
      <3>10. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
               => gate_1 = 0)'
        BY <2>3 DEF a2, TypeOK
      <3>11. (\A p \in ProcSet: pc[p] = "a4" => (
                   /\ rdv = N
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
              ))'
        BY <2>3 DEF a2, ProcSet, TypeOK
      <3>12. (gate_2 =< Cardinality(ProcsInB2))'
        BY <2>3 DEF a2, TypeOK
      <3>13. ((\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
               => gate_2 = 0)'
        BY <2>3 DEF a2, TypeOK
      <3>14. (\A p \in ProcSet: pc[p] = "a10" => (
                   /\ rdv = 0
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
              ))'
        BY <2>3 DEF a2, ProcSet, TypeOK
      <3>15. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7,
           <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
      
    <2>4. ASSUME NEW self \in 1..N,
                 a3(self)
          PROVE  Inv'
      <3>1. (gate_1 \in 0..N)'
        BY <2>4 DEF a3
      <3>2. (gate_2 \in 0..N)'
        BY <2>4 DEF a3
      <3>3. (rdv = Cardinality(ProcsInRdv))'
        BY <2>4 DEF a3, TypeOK
      <3>4. (gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"})'
        BY <2>4 DEF a3, TypeOK
      <3>5. (gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"})'
        BY <2>4 DEF a3, TypeOK
      <3>6. ((gate_1 = 0) \/ (gate_2 = 0))'
        BY <2>4 DEF a3
      <3>7. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
              => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"}))'
        BY <2>4 DEF a3, TypeOK
      <3>8. ((\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
              => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"}))'
        BY <2>4 DEF a3, TypeOK
      <3>9. (gate_1 =< Cardinality(ProcsInB1))'
        BY <2>4 DEF a3, TypeOK
      <3>10. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
               => gate_1 = 0)'
        BY <2>4 DEF a3, TypeOK
      <3>11. (\A p \in ProcSet: pc[p] = "a4" => (
                   /\ rdv = N
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
              ))'
        <4>1. rdv \in 0..N
          BY ProcSetSubSetsBound
        <4>2. CASE rdv = N
          (* 
            prove that if rdv = N, every other process must be in a6 since 
            - there cannot be another process except self in the critical sections
            - they must be in the rdv section
            - cannot be in a7 since self is in a3 (7th invariant item)
          *)
          <5>1. (pc[self] = "a4")'
            BY <2>4, <4>2 DEF a3, ProcSet, TypeOK
          <5>2. \A p \in ProcSet : (self # p) => ~lockcs(p)
            BY <2>4, <4>2, <5>1 DEF a3, ProcSet, TypeOK, LockInv
          <5>3. \A p \in ProcSet : p#self => rdvsection(p)
            BY <4>2, AllProcsInRdv
          <5>4. ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
            BY <2>4 DEF a3, ProcSet
          <5>5. \A p \in ProcSet : (self # p) => pc[p] = "a6"
            BY <5>2, <5>3, <5>4 DEF ProcSet
          <5>6. (\A p \in ProcSet : (self # p) => pc[p] = "a6")'
            BY <2>4, <4>2, <5>1, <5>5 DEF a3, ProcSet, TypeOK
          <5>7. QED
            BY <2>4, <4>2, <5>1, <5>6 DEF a3
        <4>3. CASE rdv < N
          (*
            prove that if rdv is not N, we cannot have a process in a4
            - self will move to a5 (and others will not change)
            - currently none can be there (lock exclusion)
          *)
          <5>1. (pc[self] = "a5")'
            BY <2>4, <4>3 DEF a3, ProcSet, TypeOK
          <5>2. ~(\E p \in ProcSet: pc[p] = "a4")
            BY <2>4, <4>3 DEF a3, ProcSet, LockInv
          <5>3. ~(\E p \in ProcSet: pc[p] = "a4")'
            BY <2>4, <4>3, <5>1, <5>2 DEF a3, ProcSet, TypeOK
          <5>4. QED
            BY <5>3
        <4>5. QED
          BY <4>1, <4>2, <4>3
      <3>12. (gate_2 =< Cardinality(ProcsInB2))'
        BY <2>4 DEF a3, TypeOK
      <3>13. ((\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
               => gate_2 = 0)'
        BY <2>4 DEF a3, TypeOK
      <3>14. (\A p \in ProcSet: pc[p] = "a10" => (
                   /\ rdv = 0
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
              ))'
        BY <2>4 DEF a3, TypeOK
      <3>15. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, 
           <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
    <2>5. ASSUME NEW self \in 1..N,
                 a4(self)
          PROVE  Inv'
      <3>1. (gate_1 \in 0..N)'
        BY <2>5 DEF a4, ProcSet, TypeOK
      <3>2. (gate_2 \in 0..N)'
        BY <2>5 DEF a4
      <3>3. (rdv = Cardinality(ProcsInRdv))'
        BY <2>5 DEF a4, TypeOK
      <3>4. (gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"})'
        BY <2>5 DEF a4, ProcSet, TypeOK
      <3>5. (gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"})'
        BY <2>5 DEF a4, TypeOK
      <3>6. ((gate_1 = 0) \/ (gate_2 = 0))'
        BY <2>5 DEF a4, ProcSet, TypeOK
      <3>7. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
              => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"}))'
        BY <2>5 DEF a4, TypeOK
      <3>8. ((\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
              => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"}))'
        BY <2>5 DEF a4, TypeOK
      <3>9. (gate_1 =< Cardinality(ProcsInB1))'
        (*
          This part is still true as 
          - gate_1 will be set to N
          - ProcsInB1 must be equal to ProcSet
        *)
        <4>1. (\A p \in ProcSet : (self # p) => pc[p] = "a6")
          BY <2>5 DEF a4, ProcSet
        <4>2. (\A p \in ProcSet : (self # p) => pc[p] = "a6")'
          BY <2>5, <4>1 DEF a4, ProcSet, TypeOK
        <4>3. pc'[self] = "a5"
          BY <2>5 DEF a4, ProcSet, TypeOK
        <4>4. (\A p \in ProcSet : pc[p] \in {"a5","a6"})'
          BY <2>5, <4>2, <4>3 DEF ProcSet
        <4>5. ProcsInB1' = ProcSet
          BY <4>4
        <4> HIDE DEF ProcsInB1
        <4>6. Cardinality(ProcsInB1)' = N
          BY <4>5, FS_Interval DEF ProcSet
        <4>7. gate_1' = N
          BY <2>5 DEF a4, ProcSet
        <4>8. QED
          BY <4>6, <4>7
      <3>10. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
               => gate_1 = 0)'
        BY <2>5 DEF a4, ProcSet, TypeOK
      <3>11. (\A p \in ProcSet: pc[p] = "a4" => (
                   /\ rdv = N
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
              ))'
        BY <2>5 DEF a4, TypeOK
      <3>12. (gate_2 =< Cardinality(ProcsInB2))'
        BY <2>5 DEF a4, TypeOK
      <3>13. ((\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
               => gate_2 = 0)'
        BY <2>5 DEF a4, TypeOK
      <3>14. (\A p \in ProcSet: pc[p] = "a10" => (
                   /\ rdv = 0
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
              ))'
        BY <2>5 DEF a4, TypeOK
      <3>15. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, 
           <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
    <2>6. ASSUME NEW self \in 1..N,
                 a5(self)
          PROVE  Inv'
      BY <2>6 DEF a5, TypeOK
    <2>7. ASSUME NEW self \in 1..N,
                 a6(self)
          PROVE  Inv'
      <3>1. (gate_1 \in 0..N)'
        BY <2>7 DEF a6
      <3>2. (gate_2 \in 0..N)'
        BY <2>7 DEF a6
      <3>3. (rdv = Cardinality(ProcsInRdv))'
        BY <2>7 DEF a6, TypeOK
      <3>4. (gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"})'
        (*
          This stays true since : 
          - Either gate_1 becomes 0 (the last process leaves the wait)
          - Either gate_1 stays > 0
            
            In this case there must be at least two processes inside B1
            and they cannot be between a0-a4 (reciprocal of 10th item of Invariant)
            so if self moves to a7, there still is a process between a5-a6
        *)
        <4>1. CASE gate_1' = 0
          <5>1. QED
            BY <4>1
        <4>2. CASE gate_1' > 0
          <5>1. gate_1 >= 2
            BY <2>7, <4>2 DEF a6
          <5>2. Cardinality(ProcsInB1) >= 2
            BY <5>1, ProcSetSubSetsBound
          <5>3. \E p, q \in ProcSet : (p # q) /\ p \in ProcsInB1 /\ q \in ProcsInB1
            BY <5>2, ProcSetSubSetsBound, FS_TwoElements
          <5>4. ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
            BY <5>1
          <5>5. \E p \in ProcSet: (p # self) /\ pc[p] \in {"a5", "a6"}
            BY <5>3, <5>4
          <5>6. (\E p \in ProcSet: pc[p] \in {"a5", "a6"})'
            BY <2>7, <5>5 DEF a6, ProcSet, TypeOK
          <5>7. QED
            BY <4>2, <5>6
        <4>3. QED
          BY <4>1, <4>2
      <3>5. (gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"})'
        BY <2>7 DEF a6
      <3>6. ((gate_1 = 0) \/ (gate_2 = 0))'
        BY <2>7 DEF a6
      <3>7. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
              => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"}))'
        BY <2>7 DEF a6, TypeOK
      <3>8. ((\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
              => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"}))'
        BY <2>7 DEF a6, TypeOK
      <3>9. (gate_1 =< Cardinality(ProcsInB1))'
        (*
          when self goes to a7
          - ProcsInB1 loses one element
          - gate_1 decreased by 1
          
          so comparision stays true
        *)
        <4>1. /\ gate_1' + 1 = gate_1
              /\ gate_1 \in Nat /\ gate_1' \in Nat
          BY <2>7 DEF a6
        <4>2. /\ ProcsInB1' = ProcsInB1 \ {self}
              /\ self \in ProcsInB1
          BY <2>7 DEF a6, ProcSet, TypeOK
        <4> HIDE DEF ProcsInB1
        <4>3. /\ Cardinality(ProcsInB1)' + 1 = Cardinality(ProcsInB1)
              /\ Cardinality(ProcsInB1)' \in Nat /\ Cardinality(ProcsInB1) \in Nat
          BY <4>2, ProcSetSubSetsBound, FS_RemoveElement
        <4>4. QED
          BY <4>1, <4>3
      <3>10. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
               => gate_1 = 0)'
        BY <2>7 DEF a6, TypeOK
      <3>11. (\A p \in ProcSet: pc[p] = "a4" => (
                   /\ rdv = N
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
              ))'
        BY <2>7 DEF a6, TypeOK
      <3>12. (gate_2 =< Cardinality(ProcsInB2))' 
        \* gate_2 is and stays 0 and Cardinality is in 0..N
        BY <2>7, ProcSetSubSetsBound DEF a6
      <3>13. ((\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
               => gate_2 = 0)'
        BY <2>7 DEF a6
      <3>14. (\A p \in ProcSet: pc[p] = "a10" => (
                   /\ rdv = 0
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
              ))'
        BY <2>7 DEF a6, TypeOK
      <3>15. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, 
           <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
    <2>8. ASSUME NEW self \in 1..N,
                 a7(self)
          PROVE  Inv'
      BY <2>8 DEF a7, TypeOK, LockInv, ProcSet
    <2>9. ASSUME NEW self \in 1..N,
                 a8(self)
          PROVE  Inv'
      <3>1. (gate_1 \in 0..N)'
        BY <2>9 DEF a8
      <3>2. (gate_2 \in 0..N)'
        BY <2>9 DEF a8
      <3>3. (rdv = Cardinality(ProcsInRdv))'
        <4>1. /\ ProcsInRdv \ {self} = ProcsInRdv' 
              /\ self \in ProcsInRdv
          BY <2>9 DEF a8, ProcSet, TypeOK
        <4> HIDE DEF ProcsInRdv
        <4>2. /\ IsFiniteSet(ProcsInRdv')
              /\ Cardinality(ProcsInRdv') = Cardinality(ProcsInRdv) - 1
          BY <4>1, FS_RemoveElement, ProcSetSubSetsBound
        <4>3. (rdv = Cardinality(ProcsInRdv))'
          BY <2>9, <4>2 DEF a8
        <4>4. QED
          BY <4>3
      <3>4. (gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"})'
        BY <2>9 DEF a8, TypeOK
      <3>5. (gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"})'
        BY <2>9 DEF a8, TypeOK
      <3>6. ((gate_1 = 0) \/ (gate_2 = 0))'
        BY <2>9 DEF a8
      <3>7. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
              => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"}))'
        BY <2>9 DEF a8, TypeOK
      <3>8. ((\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
              => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"}))'
        BY <2>9 DEF a8, TypeOK
      <3>9. (gate_1 =< Cardinality(ProcsInB1))'
        BY <2>9 DEF a8, TypeOK
      <3>10. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
               => gate_1 = 0)'
        BY <2>9 DEF a8, TypeOK
      <3>11. (\A p \in ProcSet: pc[p] = "a4" => (
                   /\ rdv = N
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
              ))'
        BY <2>9 DEF a8, ProcSet, TypeOK
      <3>12. (gate_2 =< Cardinality(ProcsInB2))'
        BY <2>9 DEF a8, TypeOK
      <3>13. ((\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
               => gate_2 = 0)'
        BY <2>9 DEF a8, TypeOK
      <3>14. (\A p \in ProcSet: pc[p] = "a10" => (
                   /\ rdv = 0
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
              ))'
        BY <2>9 DEF a8, ProcSet, TypeOK
      <3>15. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, 
           <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
    <2>10. ASSUME NEW self \in 1..N,
                  a9(self)
           PROVE  Inv'
      <3>1. (gate_1 \in 0..N)'
        BY <2>10 DEF a9
      <3>2. (gate_2 \in 0..N)'
        BY <2>10 DEF a9
      <3>3. (rdv = Cardinality(ProcsInRdv))'
        BY <2>10 DEF a9, TypeOK
      <3>4. (gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"})'
        BY <2>10 DEF a9, TypeOK
      <3>5. (gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"})'
        BY <2>10 DEF a9, TypeOK
      <3>6. ((gate_1 = 0) \/ (gate_2 = 0))'
        BY <2>10 DEF a9
      <3>7. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
              => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"}))'
        BY <2>10 DEF a9, TypeOK
      <3>8. ((\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
              => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"}))'
        BY <2>10 DEF a9, TypeOK
      <3>9. (gate_1 =< Cardinality(ProcsInB1))'
        BY <2>10 DEF a9, TypeOK
      <3>10. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
               => gate_1 = 0)'
        BY <2>10 DEF a9, TypeOK
      <3>11. (\A p \in ProcSet: pc[p] = "a4" => (
                   /\ rdv = N
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
              ))'
        BY <2>10 DEF a9, TypeOK
      <3>12. (gate_2 =< Cardinality(ProcsInB2))'
        BY <2>10 DEF a9, TypeOK
      <3>13. ((\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
               => gate_2 = 0)'
        BY <2>10 DEF a9, TypeOK
      <3>14. (\A p \in ProcSet: pc[p] = "a10" => (
                   /\ rdv = 0
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
              ))'
        <4>1. rdv \in 0..N
          BY ProcSetSubSetsBound
        <4>2. CASE rdv = 0
          (* 
            prove that if rdv = 0, every other process must be in a12 since :
            - there cannot be another process except self in the critical sections
            - they must be outside the rdv section
            - cannot be in a0/a1 since self is in a9 (8th invariant item)
          *)
          <5>1. (pc[self] = "a10")'
            BY <2>10, <4>2 DEF a9, ProcSet, TypeOK
          <5>2. \A p \in ProcSet : (self # p) => ~lockcs(p)
            BY <2>10, <4>2, <5>1 DEF a9, ProcSet, TypeOK, LockInv
          <5>3. \A p \in ProcSet : p#self => ~rdvsection(p)
            BY <4>2, AllProcsNotInRdv
          <5>4. ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
            BY <2>10 DEF a9, ProcSet
          <5>5. \A p \in ProcSet : (self # p) => pc[p] = "a12"
            BY <5>2, <5>3, <5>4 DEF ProcSet, TypeOK
          <5>6. (\A p \in ProcSet : (self # p) => pc[p] = "a12")'
            BY <2>10, <4>2, <5>1, <5>5 DEF a9, ProcSet, TypeOK
          <5>7. QED
            BY <2>10, <4>2, <5>1, <5>6 DEF a9
        <4>3. CASE rdv > 0
          (*
            prove that if rdv is not 0, we cannot have a process in a10
            - self will move to a11 (and others will not change)
            - currently none can be there (lock exclusion)
          *)
          <5>1. (pc[self] = "a11")'
            BY <2>10, <4>3 DEF a9, ProcSet, TypeOK
          <5>2. ~(\E p \in ProcSet: pc[p] = "a10")
            BY <2>10, <4>3 DEF a9, ProcSet, LockInv
          <5>3. ~(\E p \in ProcSet: pc[p] = "a10")'
            BY <2>10, <4>3, <5>1, <5>2 DEF a9, ProcSet, TypeOK
          <5>4. QED
            BY <5>3
        <4>5. QED
          BY <4>1, <4>2, <4>3
      <3>15. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, 
           <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
    <2>11. ASSUME NEW self \in 1..N,
                  a10(self)
           PROVE  Inv'
      <3>1. (gate_1 \in 0..N)'
        BY <2>11 DEF a10
      <3>2. (gate_2 \in 0..N)'
        BY <2>11 DEF a10, ProcSet, TypeOK
      <3>3. (rdv = Cardinality(ProcsInRdv))'
        BY <2>11 DEF a10, ProcSet, TypeOK
      <3>4. (gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"})'
        BY <2>11 DEF a10, TypeOK
      <3>5. (gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"})'
        BY <2>11 DEF a10, ProcSet, TypeOK
      <3>6. ((gate_1 = 0) \/ (gate_2 = 0))'
        BY <2>11 DEF a10, ProcSet
      <3>7. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
              => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"}))'
        BY <2>11 DEF a10, TypeOK
      <3>8. ((\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
              => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"}))'
        BY <2>11 DEF a10, TypeOK
      <3>9. (gate_1 =< Cardinality(ProcsInB1))'
        BY <2>11 DEF a10, ProcSet, TypeOK
      <3>10. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
               => gate_1 = 0)'
        BY <2>11 DEF a10, TypeOK
      <3>11. (\A p \in ProcSet: pc[p] = "a4" => (
                   /\ rdv = N
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
              ))'
        BY <2>11 DEF a10, TypeOK
      <3>12. (gate_2 =< Cardinality(ProcsInB2))'
        (*
          This part is still true as :
          - gate_2 will be set to N
          - ProcsInB2 must be equal to ProcSet
        *)
        <4>1. (\A p \in ProcSet : (self # p) => pc[p] = "a12")
          BY <2>11 DEF a10, ProcSet
        <4>2. (\A p \in ProcSet : (self # p) => pc[p] = "a12")'
          BY <2>11, <4>1 DEF a10, ProcSet, TypeOK
        <4>3. pc'[self] = "a11"
          BY <2>11 DEF a10, ProcSet, TypeOK
        <4>4. (\A p \in ProcSet : pc[p] \in {"a11","a12"})'
          BY <2>11, <4>2, <4>3 DEF ProcSet
        <4>5. ProcsInB2' = ProcSet
          BY <4>4
        <4> HIDE DEF ProcsInB2
        <4>6. Cardinality(ProcsInB2)' = N
          BY <4>5, FS_Interval DEF ProcSet
        <4>7. gate_2' = N
          BY <2>11 DEF a10, ProcSet
        <4>8. QED
          BY <4>6, <4>7
      <3>13. ((\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
               => gate_2 = 0)'
        BY <2>11 DEF a10, ProcSet, TypeOK
      <3>14. (\A p \in ProcSet: pc[p] = "a10" => (
                   /\ rdv = 0
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
              ))'
        BY <2>11 DEF a10, TypeOK
      <3>15. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, 
           <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
    <2>12. ASSUME NEW self \in 1..N,
                  a11(self)
           PROVE  Inv'
      BY <2>12 DEF a11, TypeOK
    <2>13. ASSUME NEW self \in 1..N,
                  a12(self)
           PROVE  Inv'
      <3>1. (gate_1 \in 0..N)'
        BY <2>13 DEF a12
      <3>2. (gate_2 \in 0..N)'
        BY <2>13 DEF a12
      <3>3. (rdv = Cardinality(ProcsInRdv))'
        BY <2>13 DEF a12, TypeOK
      <3>4. (gate_1 > 0 => \E p \in ProcSet : pc[p] \in {"a5", "a6"})'
        BY <2>13 DEF a12
      <3>5. (gate_2 > 0 => \E p \in ProcSet : pc[p] \in {"a11", "a12"})'
        (*
          This stays true since : 
          - Either gate_2 becomes 0 (the last process leaves the wait)
          - Either gate_2 stays > 0
            
            In this case there must be at least two processes inside B2
            and they cannot be between a7-a10 (reciprocal of 13th item of Invariant)
            so if self moves to a0, there still is a process between a11-a12
        *)
        <4>1. CASE gate_2' = 0
          <5>1. QED
            BY <4>1
        <4>2. CASE gate_2' > 0
          <5>1. gate_2 >= 2
            BY <2>13, <4>2 DEF a12
          <5>2. Cardinality(ProcsInB2) >= 2
            BY <5>1, ProcSetSubSetsBound
          <5>3. \E p, q \in ProcSet : (p # q) /\ p \in ProcsInB2 /\ q \in ProcsInB2
            BY <5>2, ProcSetSubSetsBound, FS_TwoElements
          <5>4. ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
            BY <5>1
          <5>5. \E p \in ProcSet: (p # self) /\ pc[p] \in {"a11", "a12"}
            BY <5>3, <5>4
          <5>6. (\E p \in ProcSet: pc[p] \in {"a11", "a12"})'
            BY <2>13, <5>5 DEF a12, ProcSet, TypeOK
          <5>7. QED
            BY <4>2, <5>6
        <4>3. QED
          BY <4>1, <4>2
      <3>6. ((gate_1 = 0) \/ (gate_2 = 0))'
        BY <2>13 DEF a12
      <3>7. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
              => ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"}))'
        BY <2>13 DEF a12, TypeOK
      <3>8. ((\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
              => ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"}))'
        BY <2>13 DEF a12, TypeOK
      <3>9. (gate_1 =< Cardinality(ProcsInB1))' 
        \* gate_1 is and stays 0 and Cardinality is in 0..N
        BY <2>13, ProcSetSubSetsBound DEF a12
      <3>10. ((\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
               => gate_1 = 0)'
        BY <2>13 DEF a12
      <3>11. (\A p \in ProcSet: pc[p] = "a4" => (
                   /\ rdv = N
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a6"
              ))'
        BY <2>13 DEF a12, TypeOK
      <3>12. (gate_2 =< Cardinality(ProcsInB2))'
        (*
          when self goes to a0 :
          - ProcsInB2 loses one element
          - gate_2 decreased by 1
          
          so comparision stays true
        *)
        <4>1. /\ gate_2' + 1 = gate_2
              /\ gate_2 \in Nat /\ gate_2' \in Nat
          BY <2>13 DEF a12
        <4>2. /\ ProcsInB2' = ProcsInB2 \ {self}
              /\ self \in ProcsInB2
          BY <2>13 DEF a12, ProcSet, TypeOK
        <4> HIDE DEF ProcsInB2
        <4>3. /\ Cardinality(ProcsInB2)' + 1 = Cardinality(ProcsInB2)
              /\ Cardinality(ProcsInB2)' \in Nat
          BY <4>2, ProcSetSubSetsBound, FS_RemoveElement
        <4>4. QED
          BY <4>1, <4>3
      <3>13. ((\E p \in ProcSet: pc[p] \in{"a7", "a8", "a9", "a10"})
               => gate_2 = 0)'
        BY <2>13 DEF a12, TypeOK
      <3>14. (\A p \in ProcSet: pc[p] = "a10" => (
                   /\ rdv = 0
                   /\ \A q \in ProcSet : (p # q) => pc[q] = "a12"
              ))'
        BY <2>13 DEF a12, TypeOK
      <3>15. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, 
           <3>8, <3>9, <3>10, <3>11, <3>12, <3>13, <3>14
    <2>14. CASE UNCHANGED vars
      BY <2>14 DEF vars
    <2>15. QED
      BY <2>1, <2>10, <2>11, <2>12, <2>13, <2>14, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next, proc
  <1>3. QED
    BY <1>1, <1>2, PTL, Typing, LockExclusion DEF Spec

THEOREM BarrierExclusion ==
    Inv => \/ ~(\E p \in ProcSet: pc[p] \in {"a0", "a1", "a2", "a3", "a4"})
           \/ ~(\E p \in ProcSet: pc[p] \in {"a7", "a8", "a9", "a10"})
  BY N_Assumption DEF Inv
    
THEOREM BarrierExclusion2 ==
    TypeOK /\ Inv => 
      \/ (\A p \in ProcSet: pc[p] \in 
                    {"a5", "a6", "a7", "a8", "a9", "a10", "a11", "a12"})
      \/ (\A p \in ProcSet: pc[p] \in 
                    {"a11", "a12", "a0", "a1", "a2", "a3", "a4", "a5", "a6"})
  BY N_Assumption DEF TypeOK, Inv

THEOREM FlushInvariant == Spec => []FlushInv
  <1> USE N_Assumption DEF FlushInv, ProcSet,
                           ProcsInB1, barrier1, ProcsInB2, barrier2 
  <1>1. Init => FlushInv
    BY FS_EmptySet DEF Init
  <1>2. /\ [Next]_vars
        /\ TypeOK
        /\ LockInv
        /\ Inv
        /\ FlushInv
        => FlushInv' 
    <2> SUFFICES ASSUME [Next]_vars, TypeOK, LockInv, Inv, FlushInv
                 PROVE  FlushInv'
      OBVIOUS
    <2>1. ASSUME NEW self \in 1..N, a0(self)
        PROVE FlushInv'
      BY <2>1 DEF a0, TypeOK, Inv
    <2>2. ASSUME NEW self \in 1..N, a1(self)
        PROVE FlushInv'
      BY <2>2 DEF a1, TypeOK, Inv
    <2>3. ASSUME NEW self \in 1..N, a2(self)
        PROVE FlushInv'
      BY <2>3 DEF a2, TypeOK, Inv
    <2>4. ASSUME NEW self \in 1..N, a3(self)
        PROVE FlushInv'
      BY <2>4 DEF a3, TypeOK, Inv, LockInv
    <2>5. ASSUME NEW self \in 1..N, a4(self)
        PROVE FlushInv'
      <3>1. (gate_1 > 0 => gate_1 = Cardinality(ProcsInB1))'
        <4>1. (\A p \in ProcSet : (self # p) => pc[p] = "a6")
          BY <2>5 DEF a4, Inv
        <4>2. (\A p \in ProcSet : (self # p) => pc[p] = "a6")'
          BY <2>5, <4>1 DEF a4, ProcSet, TypeOK
        <4>3. pc'[self] = "a5"
          BY <2>5 DEF a4, ProcSet, TypeOK
        <4>4. (\A p \in ProcSet : pc[p] \in {"a5","a6"})'
          BY <2>5, <4>2, <4>3 DEF ProcSet
        <4>5. ProcsInB1' = ProcSet
          BY <4>4
        <4> HIDE DEF ProcsInB1
        <4>6. Cardinality(ProcsInB1)' = N
          BY <4>5, FS_Interval DEF ProcSet
        <4>7. gate_1' = N
          BY <2>5 DEF a4, Inv
        <4>8. QED
          BY <4>6, <4>7
      <3>2. (gate_2 > 0 => gate_2 = Cardinality(ProcsInB2))'
        BY <2>5 DEF a4, TypeOK, Inv
      <3>3. QED
        BY <3>1, <3>2
    <2>6. ASSUME NEW self \in 1..N, a5(self)
        PROVE FlushInv'
      BY <2>6 DEF a5, TypeOK, Inv
    <2>7. ASSUME NEW self \in 1..N, a6(self)
        PROVE FlushInv'
      <3>1. (gate_1 > 0 => gate_1 = Cardinality(ProcsInB1))'
        <4>1. /\ gate_1' + 1 = gate_1
              /\ gate_1 \in Nat /\ gate_1' \in Nat
          BY <2>7 DEF a6, TypeOK
        <4>2. /\ ProcsInB1' = ProcsInB1 \ {self}
              /\ self \in ProcsInB1
          BY <2>7 DEF a6, TypeOK
        <4> HIDE DEF ProcsInB1
        <4>3. /\ Cardinality(ProcsInB1)' + 1 = Cardinality(ProcsInB1)
              /\ Cardinality(ProcsInB1)' \in Nat /\ Cardinality(ProcsInB1) \in Nat
          BY <4>2, ProcSetSubSetsBound, FS_RemoveElement
        <4>4. QED
          BY <4>1, <4>3
      <3>2. (gate_2 > 0 => gate_2 = Cardinality(ProcsInB2))'
        BY <2>7 DEF a6, TypeOK, Inv
      <3>3. QED
        BY <3>1, <3>2
    <2>8. ASSUME NEW self \in 1..N, a7(self)
        PROVE FlushInv'
      BY <2>8 DEF a7, TypeOK, Inv
    <2>9. ASSUME NEW self \in 1..N, a8(self)
        PROVE FlushInv'
      BY <2>9 DEF a8, TypeOK, Inv
    <2>10. ASSUME NEW self \in 1..N, a9(self)
        PROVE FlushInv'
      BY <2>10 DEF a9, TypeOK, Inv, LockInv
    <2>11. ASSUME NEW self \in 1..N, a10(self)
        PROVE FlushInv'
      <3>1. (gate_1 > 0 => gate_1 = Cardinality(ProcsInB1))'
        BY <2>11 DEF a10, TypeOK, Inv
      <3>2. (gate_2 > 0 => gate_2 = Cardinality(ProcsInB2))'
        <4>1. (\A p \in ProcSet : (self # p) => pc[p] = "a12")
          BY <2>11 DEF a10, Inv
        <4>2. (\A p \in ProcSet : (self # p) => pc[p] = "a12")'
          BY <2>11, <4>1 DEF a10, ProcSet, TypeOK
        <4>3. pc'[self] = "a11"
          BY <2>11 DEF a10, ProcSet, TypeOK
        <4>4. (\A p \in ProcSet : pc[p] \in {"a11","a12"})'
          BY <2>11, <4>2, <4>3 DEF ProcSet
        <4>5. ProcsInB2' = ProcSet
          BY <4>4
        <4> HIDE DEF ProcsInB2
        <4>6. Cardinality(ProcsInB2)' = N
          BY <4>5, FS_Interval DEF ProcSet
        <4>7. gate_2' = N
          BY <2>11 DEF a10, Inv
        <4>8. QED
          BY <4>6, <4>7
      <3>3. QED
        BY <3>1, <3>2
    <2>12. ASSUME NEW self \in 1..N, a11(self)
        PROVE FlushInv'
      BY <2>12 DEF a11, TypeOK, Inv
    <2>13. ASSUME NEW self \in 1..N, a12(self)
        PROVE FlushInv'
      <3>1. (gate_1 > 0 => gate_1 = Cardinality(ProcsInB1))'
        BY <2>13 DEF a12, TypeOK, Inv
      <3>2. (gate_2 > 0 => gate_2 = Cardinality(ProcsInB2))'
        <4>1. /\ gate_2' + 1 = gate_2
              /\ gate_2 \in Nat /\ gate_2' \in Nat
          BY <2>13 DEF a12, Inv
        <4>2. /\ ProcsInB2' = ProcsInB2 \ {self}
              /\ self \in ProcsInB2
          BY <2>13 DEF a12, TypeOK
        <4> HIDE DEF ProcsInB2
        <4>3. /\ Cardinality(ProcsInB2)' + 1 = Cardinality(ProcsInB2)
              /\ Cardinality(ProcsInB2)' \in Nat
          BY <4>2, ProcSetSubSetsBound, FS_RemoveElement
        <4>4. QED
          BY <4>1, <4>3
      <3>3. QED
        BY <3>1, <3>2
    <2>14. CASE UNCHANGED vars
        BY <2>14 DEF vars
    <2>15. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, 
         <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14
      DEF Next, proc, ProcSet
  <1>3. QED
    BY <1>1, <1>2, Typing, LockExclusion, Invariant, PTL DEF Spec
 
THEOREM Spec => B!Spec
  <1> USE DEF ProcSet, B!ProcSet, pc_translation
  <1>1. Init => B!Init
    BY DEF Init, B!Init
  <1>2. /\ [Next]_vars
        /\ TypeOK /\ TypeOK' 
        /\ LockInv /\ LockInv'
        /\ Inv /\ Inv'
        /\ FlushInv /\ FlushInv'
        => [B!Next]_B!vars
    <2> USE DEF Next, vars, B!Next, B!vars, B!b0, B!b1
    <2> SUFFICES ASSUME [Next]_vars,
                        TypeOK, TypeOK',
                        LockInv, LockInv',
                        Inv, Inv',
                        FlushInv, FlushInv'
                 PROVE [B!Next]_B!vars
      OBVIOUS
    <2>1. ASSUME NEW self \in 1..N, a0(self)
          PROVE [B!Next]_B!vars
      BY <2>1 DEF a0, TypeOK
    <2>2. ASSUME NEW self \in 1..N, a1(self)
          PROVE UNCHANGED B!vars
      BY <2>2 DEF a1, TypeOK
    <2>3. ASSUME NEW self \in 1..N, a2(self)
          PROVE UNCHANGED B!vars
      BY <2>3 DEF a2, TypeOK
    <2>4. ASSUME NEW self \in 1..N, a3(self)
          PROVE UNCHANGED B!vars
      BY <2>4 DEF a3, TypeOK
    <2>5. ASSUME NEW self \in 1..N, a4(self)
          PROVE UNCHANGED B!vars
      BY <2>5 DEF a4, TypeOK, Inv
    <2>6. ASSUME NEW self \in 1..N, a5(self)
          PROVE UNCHANGED B!vars
      BY <2>6 DEF a5, TypeOK
    <2>7. ASSUME NEW self \in 1..N, a6(self)
          PROVE UNCHANGED B!vars
      BY <2>7 DEF a6, TypeOK
    <2>8. ASSUME NEW self \in 1..N, a7(self)
          PROVE UNCHANGED B!vars
      BY <2>8 DEF a7, TypeOK
    <2>9. ASSUME NEW self \in 1..N, a8(self)
          PROVE UNCHANGED B!vars
      BY <2>9 DEF a8, TypeOK
    <2>10. ASSUME NEW self \in 1..N, a9(self)
          PROVE UNCHANGED B!vars
      BY <2>10 DEF a9, TypeOK, LockInv, Inv
    <2>11. ASSUME NEW self \in 1..N, a10(self)
          PROVE [B!Next]_B!vars
      BY <2>11 DEF a10, TypeOK, LockInv, Inv
    <2>12. ASSUME NEW self \in 1..N, a11(self)
          PROVE UNCHANGED B!vars
      BY <2>12 DEF a11, TypeOK
    <2>13. ASSUME NEW self \in 1..N, a12(self)
          PROVE UNCHANGED B!vars
      <3>1. CASE gate_2' = 0
        <4>1. /\ gate_2 = 1
              /\ Cardinality(ProcsInB2) = 1
          BY <2>13, <3>1 DEF a12, TypeOK, FlushInv
        <4>2. /\ ProcsInB2' = ProcsInB2 \ {self}
              /\ self \in ProcsInB2
          BY <2>13 DEF a12, TypeOK, ProcsInB2, barrier2
        <4>3. /\ Cardinality(ProcsInB2)' = 0
          BY <4>1, <4>2, ProcSetSubSetsBound, FS_RemoveElement
        <4>4. ~(\E p \in ProcSet : barrier2(p))'
          BY <4>3, ProcSetSubSetsBound, FS_EmptySet DEF ProcsInB2
        <4>5. QED
          BY <2>13, <4>1, <4>4 DEF a12, barrier2, TypeOK
      <3>2. CASE gate_2' > 0
        BY <2>13, <3>2 DEF a12, TypeOK, Inv
      <3>3. QED
        BY <3>1, <3>2 DEF TypeOK
    <2>14. CASE UNCHANGED vars
      BY <2>14 DEF vars
    <2>15. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7,
         <2>8, <2>9, <2>10, <2>11, <2>12, <2>13, <2>14
      DEF Next, proc
  <1>3. QED
    BY <1>1, <1>2, Typing, LockExclusion, Invariant, FlushInvariant, PTL 
    DEF Spec, B!Spec
===============================================================================
