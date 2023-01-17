------------------------------- MODULE MCNano -------------------------------
(***************************************************************************)
(* This spec tries to make the Nano.tla spec model-checkable. The          *)
(* CalculateHash constant is the greatest source of trouble. The way this  *)
(* works is by playing fast and loose with TLC's level checker: it will    *)
(* rightfully error out if we instantiate the Nano spec with a variable-   *)
(* level function directly, but if we instead also make CalculateHash a    *)
(* constant in this spec then override it with a variable-level function   *)
(* *in the model* then all is well. The specific operator used is the      *)
(* CalculateHashImpl operator defined down below. See discussion here:     *)
(*                                                                         *)
(* https://groups.google.com/g/tlaplus/c/r5sB2vgil_Q/m/lM546pjpAQAJ        *)
(*                                                                         *)
(* The action StutterWhenHashesDepleted also serves as a state restriction *)
(* to gracefully terminate the spec when we have run out of hashes. We     *)
(* also make use of the VIEW functionality to remove specific hash order   *)
(* from consideration when calculating whether we have visited a state.    *)
(* It would make sense to declare the Hash set symmetric, but since this   *)
(* set gets fairly large by modelchecking standards (5+ elements) the      *)
(* computation becomes dominated by substituting all 5+! permutations of   *)
(* the set while generating new states, so actually increases modelcheck   *)
(* time.                                                                   *)
(*                                                                         *)
(* Unfortunately blockchains by their very nature have super-exponential   *)
(* scaling in the number of possible states as a function of chain length, *)
(* because the order of actions is recorded in the chain itself. This is   *)
(* the same issue faced when using any sort of history variable in finite  *)
(* modelchecking: all action order permutations are explored, not just     *)
(* combinations. Thus finite modelchecking is not very effective at        *)
(* analyzing blockchains and formal proofs should be used instead.         *)
(*                                                                         *)
(***************************************************************************)

EXTENDS
  Naturals,
  FiniteSets

CONSTANTS
  CalculateHash(_,_,_),
  Hash,
  NoHashVal,
  PrivateKey,
  PublicKey,
  Node,
  GenesisBalance,
  NoBlockVal

ASSUME
  /\ Cardinality(PrivateKey) = Cardinality(PublicKey)
  /\ Cardinality(PrivateKey) <= Cardinality(Node)
  /\ GenesisBalance \in Nat

VARIABLES
  hashFunction,
  lastHash,
  distributedLedger,
  received

Vars == <<hashFunction, lastHash, distributedLedger, received>>

\* Ignore hashFunction and lastHash when calculating state hash
View == <<distributedLedger, received>>

-----------------------------------------------------------------------------

KeyPair ==
    CHOOSE mapping \in [PrivateKey -> PublicKey] :
        /\ \A publicKey \in PublicKey :
            /\ \E privateKey \in PrivateKey :
                /\ mapping[privateKey] = publicKey

Ownership ==
    CHOOSE mapping \in [Node -> PrivateKey] :
        /\ \A privateKey \in PrivateKey :
            /\ \E node \in Node :
                /\ mapping[node] = privateKey

N == INSTANCE Nano

UndefinedHashesExist ==
  \E hash \in Hash: hashFunction[hash] = N!NoBlock

HashOf(block) ==
  IF \E hash \in Hash : hashFunction[hash] = block
  THEN CHOOSE hash \in Hash : hashFunction[hash] = block
  ELSE CHOOSE hash \in Hash : hashFunction[hash] = N!NoBlock

CalculateHashImpl(block, oldLastHash, newLastHash) ==
  LET hash == HashOf(block) IN
  /\ newLastHash = hash
  /\ hashFunction' = [hashFunction EXCEPT ![hash] = block]

TypeInvariant ==
  /\ hashFunction \in [Hash -> N!Block \cup {N!NoBlock}]
  /\ N!TypeInvariant

SafetyInvariant ==
  /\ N!SafetyInvariant

Init ==
  /\ hashFunction = [hash \in Hash |-> N!NoBlock]
  /\ N!Init

StutterWhenHashesDepleted ==
  /\ UNCHANGED hashFunction
  /\ UNCHANGED lastHash
  /\ UNCHANGED distributedLedger
  /\ UNCHANGED received

Next ==
  IF UndefinedHashesExist
  THEN N!Next
  ELSE StutterWhenHashesDepleted

Spec ==
  /\ Init
  /\ [][Next]_Vars

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

=============================================================================

