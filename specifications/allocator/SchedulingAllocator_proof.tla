--------------------- MODULE SchedulingAllocator_proof ---------------------
(***************************************************************************)
(* TLAPS proofs of the safety theorems stated in SchedulingAllocator.tla:  *)
(*                                                                         *)
(*   Allocator => []TypeInvariant                                          *)
(*   Allocator => []ResourceMutex                                          *)
(*                                                                         *)
(* TypeInvariant is directly inductive (the only subtlety is that         *)
(* Drop(sched, i) and sched \circ sq stay in Seq(Clients)).  ResourceMutex *)
(* uses the same argument as in SimpleAllocator: an Allocate(c, S) action *)
(* takes S from `available`, so S is disjoint from every alloc[c'].       *)
(*                                                                         *)
(* AllocatorInvariant is left as future work; its preservation across the *)
(* Schedule action requires careful reasoning about Range(sched \circ sq) *)
(* and the way toSchedule changes.                                       *)
(***************************************************************************)
EXTENDS SchedulingAllocator, Integers, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

(***************************************************************************)
(* The PermSeqs proof needs Clients to be finite (PermSeqs is the set of   *)
(* permutation sequences over a finite set; the recursion well-founds only *)
(* over finite subsets).  Resources is already finite by the spec's        *)
(* SchedulingAllocatorAssumptions; we add Clients here.                    *)
(***************************************************************************)
ASSUME ClientsFinite == IsFiniteSet(Clients)

(***************************************************************************)
(*                          Allocator => []TypeInvariant                   *)
(***************************************************************************)

LEMMA SubSeqInRange ==
  ASSUME NEW T, NEW s \in Seq(T), NEW m \in Int, NEW n \in Int,
         m >= 1, n <= Len(s)
  PROVE  SubSeq(s, m, n) \in Seq(T)
<1>1. \A i \in m..n : s[i] \in T
  OBVIOUS
<1>. QED  BY <1>1, SubSeqProperties

LEMMA ConcatType ==
  ASSUME NEW T, NEW s1 \in Seq(T), NEW s2 \in Seq(T)
  PROVE  s1 \o s2 \in Seq(T)
  OBVIOUS

LEMMA DropType ==
  ASSUME NEW T, NEW s \in Seq(T), NEW i \in 1..Len(s)
  PROVE  Drop(s, i) \in Seq(T)
<1>1. SubSeq(s, 1, i-1) \in Seq(T)
  BY SubSeqInRange
<1>2. SubSeq(s, i+1, Len(s)) \in Seq(T)
  BY SubSeqInRange
<1>. QED  BY <1>1, <1>2, ConcatType DEF Drop

(***************************************************************************)
(* Permutations of a finite set, packaged as sequences, are sequences over *)
(* (a superset of) the set.  The recursion in PermSeqs builds each output *)
(* by Append-ing elements of S, so the result is a sequence whose elements *)
(* are all from S \subseteq T.                                             *)
(*                                                                         *)
(* The proof has the same shape as MaximumProp in PaxosCommit_proof:       *)
(*   - PermsRec / PermsFn give the inner CHOOSE-defined recursive function;*)
(*   - PermsFnRec is the recursion equation (via WFInductiveDef);          *)
(*   - PermSeqsIsPermsFn ties PermSeqs(S) to PermsFn(S)[S];                *)
(*   - PermSeqsType then proves the property by FS_WFInduction.            *)
(***************************************************************************)
PermsRec(g, ss) ==
  IF ss = {} THEN { << >> }
  ELSE LET ps == [ x \in ss |->
                   { Append(sq, x) : sq \in g[ss \ {x}] } ]
       IN  UNION { ps[x] : x \in ss }

PermsFn(S) == CHOOSE g : g = [ss \in SUBSET S |-> PermsRec(g, ss)]

(***************************************************************************)
(* Equivalent unfold-form for non-empty ss; the LET binding can be         *)
(* eliminated by substituting ps[x] inline.                                 *)
(***************************************************************************)
LEMMA PermsRecNonempty ==
  ASSUME NEW g, NEW ss, ss # {}
  PROVE  PermsRec(g, ss) =
           UNION { { Append(sq, x) : sq \in g[ss \ {x}] } : x \in ss }
  <1>. DEFINE ps == [ x \in ss |->
                       { Append(sq, x) : sq \in g[ss \ {x}] } ]
  <1>1. PermsRec(g, ss) = UNION { ps[x] : x \in ss }
    BY Zenon DEF PermsRec
  <1>2. \A x \in ss : ps[x] = { Append(sq, x) : sq \in g[ss \ {x}] }
    OBVIOUS
  <1>3. UNION { ps[x] : x \in ss } =
          UNION { { Append(sq, x) : sq \in g[ss \ {x}] } : x \in ss }
    BY <1>2
  <1>. QED  BY <1>1, <1>3

LEMMA PermsFnRec ==
  ASSUME NEW S, IsFiniteSet(S), NEW ss \in SUBSET S
  PROVE  PermsFn(S)[ss] = PermsRec(PermsFn(S), ss)
  <1>. DEFINE perms == PermsFn(S)
  <1>0a. FiniteSubsetsOf(S) = SUBSET S
    BY FS_FiniteSubsetsOfFinite
  <1>0b. IsWellFoundedOn(StrictSubsetOrdering(S), FiniteSubsetsOf(S))
    BY FS_StrictSubsetOrderingWellFounded
  <1>0c. WFDefOn(StrictSubsetOrdering(S), FiniteSubsetsOf(S), PermsRec)
    <2>. SUFFICES ASSUME NEW g, NEW h, NEW U \in FiniteSubsetsOf(S),
                         \A V \in SetLessThan(U, StrictSubsetOrdering(S),
                                              FiniteSubsetsOf(S)) :
                              g[V] = h[V]
                  PROVE  PermsRec(g, U) = PermsRec(h, U)
      BY Isa DEF WFDefOn
    <2>1. CASE U = {}  BY <2>1 DEF PermsRec
    <2>2. CASE U # {}
      <3>1. ASSUME NEW x \in U
            PROVE  /\ U \ {x} \in FiniteSubsetsOf(S)
                   /\ <<U \ {x}, U>> \in StrictSubsetOrdering(S)
                   /\ U \ {x} \in SetLessThan(U, StrictSubsetOrdering(S),
                                              FiniteSubsetsOf(S))
                   /\ g[U \ {x}] = h[U \ {x}]
        <4>1. U \in SUBSET S /\ IsFiniteSet(U)
          BY DEF FiniteSubsetsOf
        <4>2. IsFiniteSet(U \ {x})
          BY <4>1, FS_RemoveElement
        <4>3. U \ {x} \in FiniteSubsetsOf(S)
          BY <4>1, <4>2 DEF FiniteSubsetsOf
        <4>4. <<U \ {x}, U>> \in StrictSubsetOrdering(S)
          BY <3>1, <4>1 DEF StrictSubsetOrdering
        <4>5. U \ {x} \in SetLessThan(U, StrictSubsetOrdering(S),
                                       FiniteSubsetsOf(S))
          BY <4>3, <4>4 DEF SetLessThan
        <4>6. g[U \ {x}] = h[U \ {x}]
          BY <4>5
        <4>. QED  BY <4>3, <4>4, <4>5, <4>6
      <3>2. \A x \in U : g[U \ {x}] = h[U \ {x}]
        BY <3>1
      <3>3. PermsRec(g, U) =
              UNION { { Append(sq, x) : sq \in g[U \ {x}] } : x \in U }
        BY <2>2, PermsRecNonempty
      <3>4. PermsRec(h, U) =
              UNION { { Append(sq, x) : sq \in h[U \ {x}] } : x \in U }
        BY <2>2, PermsRecNonempty
      <3>. QED  BY <3>2, <3>3, <3>4
    <2>. QED  BY <2>1, <2>2
  <1>0d. OpDefinesFcn(perms, FiniteSubsetsOf(S), PermsRec)
    BY <1>0a, Isa DEF OpDefinesFcn, PermsFn
  <1>1. WFInductiveDefines(perms, FiniteSubsetsOf(S), PermsRec)
    BY <1>0b, <1>0c, <1>0d, WFInductiveDef, Isa
  <1>2. perms = [x \in FiniteSubsetsOf(S) |-> PermsRec(perms, x)]
    BY <1>1, Zenon DEF WFInductiveDefines
  <1>3. ss \in FiniteSubsetsOf(S)
    BY <1>0a
  <1>. QED  BY <1>2, <1>3, Zenon

LEMMA PermSeqsIsPermsFn ==
  ASSUME NEW S
  PROVE  PermSeqs(S) = PermsFn(S)[S]
  BY Zenon DEF PermSeqs, PermsFn, PermsRec

LEMMA PermSeqsType ==
  ASSUME NEW T, NEW S \in SUBSET T, IsFiniteSet(S),
         NEW sq \in PermSeqs(S)
  PROVE  sq \in Seq(T)
  <1>. DEFINE perms == PermsFn(S)
  <1>. DEFINE Q(ss) == \A sq2 \in perms[ss] : sq2 \in Seq(T)
  <1>1. ASSUME NEW ss \in SUBSET S,
               \A U \in (SUBSET ss) \ {ss} : Q(U)
        PROVE  Q(ss)
    <2>0. perms[ss] = PermsRec(perms, ss)
      BY PermsFnRec
    <2>1. CASE ss = {}
      <3>1. perms[ss] = {<<>>}
        BY <2>0, <2>1 DEF PermsRec
      <3>2. <<>> \in Seq(T)
        BY EmptySeq
      <3>. QED  BY <3>1, <3>2
    <2>2. CASE ss # {}
      <3>. SUFFICES ASSUME NEW sq2 \in perms[ss]
                    PROVE  sq2 \in Seq(T)
        OBVIOUS
      <3>1. perms[ss] =
              UNION { { Append(sq3, x) : sq3 \in perms[ss \ {x}] } : x \in ss }
        BY <2>0, <2>2, PermsRecNonempty
      <3>2. PICK x \in ss : sq2 \in { Append(sq3, x) : sq3 \in perms[ss \ {x}] }
        BY <3>1
      <3>3. PICK sq3 \in perms[ss \ {x}] : sq2 = Append(sq3, x)
        BY <3>2
      <3>4. ss \ {x} \in (SUBSET ss) \ {ss}
        BY <3>2
      <3>5. Q(ss \ {x})
        BY <1>1, <3>4
      <3>6. sq3 \in Seq(T)
        BY <3>3, <3>5
      <3>7. x \in T
        BY <3>2, S \in SUBSET T
      <3>. QED  BY <3>3, <3>6, <3>7, AppendProperties
    <2>. QED  BY <2>1, <2>2
  <1>2. Q(S)
    <2>. HIDE DEF Q
    <2>. QED  BY <1>1, FS_WFInduction, IsaM("iprover")
  <1>3. sq \in perms[S]
    BY PermSeqsIsPermsFn
  <1>. QED  BY <1>2, <1>3

THEOREM TypeCorrect == Allocator => []TypeInvariant
<1>1. Init => TypeInvariant
  BY DEF Init, TypeInvariant
<1>2. TypeInvariant /\ [Next]_vars => TypeInvariant'
  <2> SUFFICES ASSUME TypeInvariant, [Next]_vars
               PROVE  TypeInvariant'
    OBVIOUS
  <2>. USE DEF TypeInvariant
  <2>1. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Request(c, S)
        PROVE  TypeInvariant'
    BY <2>1 DEF Request
  <2>2. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Allocate(c, S)
        PROVE  TypeInvariant'
    \* alloc' EXCEPT, unsat' EXCEPT.  sched' = Drop(sched, i) or sched.
    <3>1. PICK i \in DOMAIN sched :
                /\ sched[i] = c
                /\ \A j \in 1..i-1 : unsat[sched[j]] \cap S = {}
                /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
      BY <2>2 DEF Allocate
    <3>2. unsat' \in [Clients -> SUBSET Resources]
      BY <2>2 DEF Allocate
    <3>3. alloc' \in [Clients -> SUBSET Resources]
      BY <2>2 DEF Allocate
    <3>4. i \in 1..Len(sched)
      BY <3>1
    <3>5. sched' \in Seq(Clients)
      BY <3>1, <3>4, DropType
    <3>. QED  BY <3>2, <3>3, <3>5
  <2>3. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Return(c, S)
        PROVE  TypeInvariant'
    BY <2>3 DEF Return
  <2>4. CASE Schedule
    <3>1. PICK sq \in PermSeqs(toSchedule) : sched' = sched \o sq
      BY <2>4 DEF Schedule
    <3>2. toSchedule \subseteq Clients
      BY DEF toSchedule
    <3>2a. IsFiniteSet(toSchedule)
      BY <3>2, ClientsFinite, FS_Subset
    <3>3. sq \in Seq(Clients)
      BY <3>1, <3>2, <3>2a, PermSeqsType
    <3>4. sched' \in Seq(Clients)
      BY <3>1, <3>3, ConcatType
    <3>. QED  BY <2>4, <3>4 DEF Schedule
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Allocator

(***************************************************************************)
(*                          Allocator => []ResourceMutex                   *)
(***************************************************************************)

Inv == TypeInvariant /\ ResourceMutex

THEOREM Mutex == Allocator => []ResourceMutex
<1>1. Init => Inv
  BY DEF Init, Inv, TypeInvariant, ResourceMutex
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>. USE DEF Inv, TypeInvariant, ResourceMutex
  <2>1. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Request(c, S)
        PROVE  Inv'
    BY <2>1 DEF Request
  <2>2. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Allocate(c, S)
        PROVE  Inv'
    \* Same argument as SimpleAllocator: S \subseteq available =>
    \* S \cap alloc[c'] = {} for all c'.
    <3>0. TypeInvariant'
      \* re-derive via the TypeCorrect step proof (inlined).
      <4>1. PICK i \in DOMAIN sched :
                  /\ sched[i] = c
                  /\ \A j \in 1..i-1 : unsat[sched[j]] \cap S = {}
                  /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
        BY <2>2 DEF Allocate
      <4>2. i \in 1..Len(sched)
        BY <4>1
      <4>3. sched' \in Seq(Clients)
        BY <4>1, <4>2, DropType
      <4>. QED  BY <2>2, <4>3 DEF Allocate
    <3>2. alloc' = [alloc EXCEPT ![c] = @ \cup S]
      BY <2>2 DEF Allocate
    <3>3. \A cc \in Clients : alloc'[cc] = IF cc = c THEN alloc[cc] \cup S
                                                      ELSE alloc[cc]
      BY <3>2
    <3>4. S \subseteq available
      BY <2>2 DEF Allocate
    <3>5. \A cc \in Clients : S \cap alloc[cc] = {}
      BY <3>4 DEF available
    <3>9. ResourceMutex'
      <4>1. SUFFICES ASSUME NEW c1 \in Clients, NEW c2 \in Clients, c1 # c2
                     PROVE  alloc'[c1] \cap alloc'[c2] = {}
        BY DEF ResourceMutex
      <4>6. CASE c1 = c
        <5>1. alloc'[c1] = alloc[c] \cup S
          BY <3>3, <4>6
        <5>2. alloc'[c2] = alloc[c2]
          BY <3>3, <4>6, <4>1
        <5>3. alloc[c] \cap alloc[c2] = {}
          BY <4>6, <4>1
        <5>4. S \cap alloc[c2] = {}
          BY <3>5
        <5>. QED  BY <5>1, <5>2, <5>3, <5>4
      <4>7. CASE c2 = c
        <5>1. alloc'[c2] = alloc[c] \cup S
          BY <3>3, <4>7
        <5>2. alloc'[c1] = alloc[c1]
          BY <3>3, <4>7, <4>1
        <5>3. alloc[c1] \cap alloc[c] = {}
          BY <4>7, <4>1
        <5>4. alloc[c1] \cap S = {}
          BY <3>5
        <5>. QED  BY <5>1, <5>2, <5>3, <5>4
      <4>8. CASE c1 # c /\ c2 # c
        <5>1. alloc'[c1] = alloc[c1] /\ alloc'[c2] = alloc[c2]
          BY <3>3, <4>8
        <5>. QED  BY <5>1, <4>1
      <4>. QED  BY <4>6, <4>7, <4>8
    <3>. QED  BY <3>0, <3>9 DEF Inv
  <2>3. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Return(c, S)
        PROVE  Inv'
    \* (alloc[c] \ S) \cap alloc[c'] \subseteq alloc[c] \cap alloc[c'] = {}.
    BY <2>3 DEF Return
  <2>4. CASE Schedule
    \* alloc unchanged.
    <3>1. PICK sq \in PermSeqs(toSchedule) : sched' = sched \o sq
      BY <2>4 DEF Schedule
    <3>2. toSchedule \subseteq Clients
      BY DEF toSchedule
    <3>2a. IsFiniteSet(toSchedule)
      BY <3>2, ClientsFinite, FS_Subset
    <3>3. sq \in Seq(Clients)
      BY <3>1, <3>2, <3>2a, PermSeqsType
    <3>4. sched' \in Seq(Clients)
      BY <3>1, <3>3, ConcatType
    <3>. QED  BY <2>4, <3>4 DEF Schedule
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Allocator, Inv

============================================================================
