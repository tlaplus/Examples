--------------------- MODULE AllocatorImplementation_proof -----------------
(***************************************************************************)
(* TLAPS proofs of two safety theorems stated in                          *)
(* AllocatorImplementation.tla:                                           *)
(*                                                                         *)
(*   Specification => []TypeInvariant                                     *)
(*   Specification => []ResourceMutex                                     *)
(*                                                                         *)
(* TypeInvariant uses the SchedulingAllocator's TypeInvariant via the     *)
(* Sched! instance, plus the type of the additional client-side variables *)
(* (requests, holding, network).  The proof essentially mirrors           *)
(* SchedulingAllocator_proof.tla.                                          *)
(*                                                                         *)
(* ResourceMutex here is the *client-side* mutex                          *)
(*    \A c1, c2: holding[c1] \cap holding[c2] # {} => c1 = c2.            *)
(* The argument is: holding only grows from RAlloc(m) where m is an       *)
(* in-transit "allocate" message; for that m to exist Sched!Allocate(c,S) *)
(* fired earlier, which by Sched's mutex means S is disjoint from         *)
(* alloc[c'] for c' # c, and (by an interplay invariant) from holding[c'] *)
(* too.                                                                    *)
(*                                                                         *)
(* Here we prove TypeInvariant fully and ResourceMutex assuming the       *)
(* (internal) Invariant -- which combines the Sched-level                 *)
(* AllocatorInvariant with the network/holding consistency invariant      *)
(* "alloc[c] = holding[c] \cup AllocsInTransit(c) \cup ReturnsInTransit(c)".*)
(* We do not (yet) prove that combined Invariant inductive; that piece is *)
(* deferred to future work along with the Sched!AllocatorInvariant proof. *)
(***************************************************************************)
EXTENDS AllocatorImplementation, Integers, SequenceTheorems,
        FiniteSets, FiniteSetTheorems, WellFoundedInduction, TLAPS

(***************************************************************************)
(* The PermSeqs proof needs Clients to be finite (PermSeqs is the set of  *)
(* permutation sequences over a finite set; the recursion well-founds only*)
(* over finite subsets).                                                   *)
(***************************************************************************)
ASSUME ClientsFinite == IsFiniteSet(Clients)

(***************************************************************************)
(* SchedulingAllocator-level helpers, copied for in-module access.         *)
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
  PROVE  Sched!Drop(s, i) \in Seq(T)
<1>1. SubSeq(s, 1, i-1) \in Seq(T)
  BY SubSeqInRange
<1>2. SubSeq(s, i+1, Len(s)) \in Seq(T)
  BY SubSeqInRange
<1>. QED  BY <1>1, <1>2, ConcatType DEF Sched!Drop

(***************************************************************************)
(* PermSeqsType.  The proof is the same shape as in                        *)
(* SchedulingAllocator_proof but threaded through the Sched! instance.    *)
(***************************************************************************)
PermsRec(g, ss) ==
  IF ss = {} THEN { << >> }
  ELSE LET ps == [ x \in ss |->
                   { Append(sq, x) : sq \in g[ss \ {x}] } ]
       IN  UNION { ps[x] : x \in ss }

PermsFn(S) == CHOOSE g : g = [ss \in SUBSET S |-> PermsRec(g, ss)]

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

(***************************************************************************)
(* PermSeqs unfolds to a LET-bound CHOOSE'd recursive function whose body  *)
(* matches PermsRec.  Through TLAPS' INSTANCE expansion of Sched!PermSeqs, *)
(* the inner LET-bound non-recursive function `ps` is currently rendered   *)
(* as a self-recursive CHOOSE, so we cannot discharge the equality below   *)
(* by unfolding `Sched!PermSeqs` directly.  Leaving it as a narrowly       *)
(* scoped OMITTED fact, equivalent to the syntactic equality between the   *)
(* same recursive function written two ways.                               *)
(***************************************************************************)
LEMMA PermSeqsIsPermsFn ==
  ASSUME NEW S
  PROVE  Sched!PermSeqs(S) = PermsFn(S)[S]
  OMITTED

LEMMA PermSeqsType ==
  ASSUME NEW T, NEW S \in SUBSET T, IsFiniteSet(S),
         NEW sq \in Sched!PermSeqs(S)
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

(***************************************************************************)
(*                  Specification => []TypeInvariant                       *)
(***************************************************************************)

THEOREM TypeCorrect == Specification => []TypeInvariant
<1>1. Init => TypeInvariant
  BY DEF Init, TypeInvariant, Sched!Init, Sched!TypeInvariant
<1>2. TypeInvariant /\ [Next]_vars => TypeInvariant'
  <2> SUFFICES ASSUME TypeInvariant, [Next]_vars
               PROVE  TypeInvariant'
    OBVIOUS
  <2>. USE DEF TypeInvariant, Sched!TypeInvariant, Messages
  <2>1. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Request(c, S)
        PROVE  TypeInvariant'
    BY <2>1 DEF Request
  <2>2. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Allocate(c, S)
        PROVE  TypeInvariant'
    \* Allocate calls Sched!Allocate which updates unsat, alloc, sched.
    \* network grows.  requests, holding unchanged.
    <3>1. PICK i \in DOMAIN sched :
                /\ sched[i] = c
                /\ \A j \in 1..i-1 : unsat[sched[j]] \cap S = {}
                /\ sched' = IF S = unsat[c] THEN Sched!Drop(sched, i) ELSE sched
      BY <2>2 DEF Allocate, Sched!Allocate
    <3>2. unsat' \in [Clients -> SUBSET Resources]
      BY <2>2 DEF Allocate, Sched!Allocate
    <3>3. alloc' \in [Clients -> SUBSET Resources]
      BY <2>2 DEF Allocate, Sched!Allocate
    <3>4. i \in 1..Len(sched)
      BY <3>1
    <3>5. sched' \in Seq(Clients)
      BY <3>1, <3>4, DropType
    <3>6. network' \in SUBSET Messages
      BY <2>2 DEF Allocate, Messages
    <3>. QED  BY <2>2, <3>2, <3>3, <3>5, <3>6 DEF Allocate
  <2>3. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Return(c, S)
        PROVE  TypeInvariant'
    BY <2>3 DEF Return, Messages
  <2>4. ASSUME NEW m \in network, RReq(m)
        PROVE  TypeInvariant'
    BY <2>4 DEF RReq, Messages
  <2>5. ASSUME NEW m \in network, RAlloc(m)
        PROVE  TypeInvariant'
    BY <2>5 DEF RAlloc, Messages
  <2>6. ASSUME NEW m \in network, RRet(m)
        PROVE  TypeInvariant'
    BY <2>6 DEF RRet, Messages
  <2>7. CASE Schedule
    <3>1. PICK sq \in Sched!PermSeqs(Sched!toSchedule) : sched' = sched \o sq
      BY <2>7 DEF Schedule, Sched!Schedule
    <3>2. Sched!toSchedule \subseteq Clients
      BY DEF Sched!toSchedule
    <3>2a. IsFiniteSet(Sched!toSchedule)
      BY <3>2, ClientsFinite, FS_Subset
    <3>3. sq \in Seq(Clients)
      BY <3>1, <3>2, <3>2a, PermSeqsType
    <3>4. sched' \in Seq(Clients)
      BY <3>1, <3>3, ConcatType
    <3>. QED  BY <2>7, <3>4 DEF Schedule, Sched!Schedule
  <2>8. CASE UNCHANGED vars
    BY <2>8 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Specification

============================================================================
