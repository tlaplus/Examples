------------------------------- MODULE NanoMC -------------------------------
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
(*                                                                         *)
(***************************************************************************)


EXTENDS
    Naturals,
    FiniteSets,
    TLC

CONSTANTS
    CalculateHash(_,_,_),
    HashVal,
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

HashValSymmetric == Permutations(HashVal)

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

View == <<distributedLedger, received>>

Vars == <<hashFunction, lastHash, distributedLedger, received>>

-----------------------------------------------------------------------------

RECURSIVE ReduceSet(_,_,_)
ReduceSet(op(_, _), set, acc) ==
    IF set = {}
    THEN acc
    ELSE
        LET x == CHOOSE x \in set : TRUE IN
        op(x, ReduceSet(op, set \ {x}, acc))

Hash == [
    account : PublicKey,
    value   : HashVal
]

NoHash == CHOOSE hash : hash \notin Hash

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

UndefinedHashesExistFor(account) ==
  /\ \E hashVal \in HashVal : hashFunction[account][hashVal] = NoBlockVal

UndefinedHashesExist ==
    \E account \in PublicKey : UndefinedHashesExistFor(account)

PublicKeyOf(block) ==
    IF block.type \in {"genesis", "open"}
    THEN block.account
    ELSE block.previous.account

HashOf(block) ==
    IF \E hash \in Hash : hashFunction[hash.account][hash.value] = block
    THEN CHOOSE hash \in Hash : hashFunction[hash.account][hash.value] = block
    ELSE
      LET account == PublicKeyOf(block) IN
      IF UndefinedHashesExistFor(account)
      THEN CHOOSE hash \in Hash : hash.account = account /\ hashFunction[hash.account][hash.value] = N!NoBlock
      ELSE NoHash

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    LET hash == HashOf(block) IN
    /\ hash /= NoHash
    /\ newLastHash = hash
    /\ hashFunction' = [hashFunction EXCEPT ![hash.account][hash.value] = block]

TypeInvariant ==
    /\ hashFunction \in [PublicKey -> [HashVal -> N!Block \cup {N!NoBlock}]]
    /\ N!TypeInvariant

SafetyInvariant ==
    /\ N!SafetyInvariant

Init ==
    /\ hashFunction = [key \in PublicKey |-> [hash \in HashVal |-> NoBlockVal]]
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

NanoView ==
    <<hashFunction, distributedLedger, received>>

=============================================================================

