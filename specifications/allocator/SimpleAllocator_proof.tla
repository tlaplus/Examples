----------------------- MODULE SimpleAllocator_proof -----------------------
(***************************************************************************)
(* TLAPS proofs of two safety properties of the SimpleAllocator spec:      *)
(*                                                                         *)
(*   SimpleAllocator => []TypeInvariant                                    *)
(*   SimpleAllocator => []ResourceMutex                                    *)
(*                                                                         *)
(* TypeInvariant is directly inductive.  ResourceMutex needs TypeInvariant *)
(* together with the simple observation that an Allocate(c, S) action      *)
(* takes S from the `available` resources, so S is disjoint from every     *)
(* alloc[c'] for c' # c.                                                  *)
(***************************************************************************)
EXTENDS SimpleAllocator, TLAPS

(***************************************************************************)
(*                       SimpleAllocator => []TypeInvariant                *)
(***************************************************************************)

THEOREM TypeCorrect == SimpleAllocator => []TypeInvariant
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
    BY <2>2 DEF Allocate
  <2>3. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Return(c, S)
        PROVE  TypeInvariant'
    BY <2>3 DEF Return
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF SimpleAllocator

(***************************************************************************)
(*                       SimpleAllocator => []ResourceMutex                *)
(***************************************************************************)

(***************************************************************************)
(* The combined inductive invariant.  We need TypeInvariant in scope to   *)
(* type-check alloc[c]; ResourceMutex on its own is preserved given       *)
(* TypeInvariant.                                                         *)
(***************************************************************************)
Inv == TypeInvariant /\ ResourceMutex

THEOREM Mutex == SimpleAllocator => []ResourceMutex
<1>1. Init => Inv
  BY DEF Init, Inv, TypeInvariant, ResourceMutex
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>. USE DEF Inv, TypeInvariant, ResourceMutex
  <2>1. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Request(c, S)
        PROVE  Inv'
    \* alloc unchanged.
    BY <2>1 DEF Request
  <2>2. ASSUME NEW c \in Clients, NEW S \in SUBSET Resources, Allocate(c, S)
        PROVE  Inv'
    \* alloc'[c] = alloc[c] \cup S; for c' # c, alloc'[c'] = alloc[c'].
    \* S \subseteq available means S \cap (UNION {alloc[c''] : c'' \in Clients}) = {},
    \* so in particular S \cap alloc[c'] = {} for any c'.  Combined with
    \* the IH alloc[c] \cap alloc[c'] = {}, the new alloc'[c] is still
    \* disjoint from alloc'[c'].
    <3>0. TypeInvariant'
      BY <2>2 DEF Allocate
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
    \* alloc'[c] = alloc[c] \ S; for c' # c, alloc'[c'] = alloc[c'].
    \* (alloc[c] \ S) \cap alloc[c'] \subseteq alloc[c] \cap alloc[c'] = {}.
    BY <2>3 DEF Return
  <2>4. CASE UNCHANGED vars
    BY <2>4 DEF vars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF SimpleAllocator, Inv

============================================================================
