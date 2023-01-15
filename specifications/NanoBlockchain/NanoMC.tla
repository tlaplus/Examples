------------------------------- MODULE NanoMC -------------------------------

EXTENDS
    Naturals,
    Sequences,
    FiniteSets

CONSTANTS
    CalculateHash(_,_,_),
    MaxHashCount,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

ASSUME
    /\ MaxHashCount \in Nat
    /\ Cardinality(PrivateKey) = Cardinality(PublicKey)
    /\ Cardinality(PrivateKey) <= Cardinality(Node)
    /\ GenesisBalance \in Nat

-----------------------------------------------------------------------------

RECURSIVE ReduceSet(_,_,_)
ReduceSet(op(_, _), set, acc) ==
    IF set = {}
    THEN acc
    ELSE
        LET x == CHOOSE x \in set : TRUE IN
        op(x, ReduceSet(op, set \ {x}, acc))

Hash ==
    [account    : PublicKey,
    sequence    : 1 .. MaxHashCount]

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
    /\ \E key \in PublicKey : Len(hashFunction[key]) < MaxHashCount

HashIsDefined(block) ==
    /\ \E hash \in Hash :
        /\ hash.sequence \in DOMAIN hashFunction[hash.account]
        /\ hashFunction[hash.account][hash.sequence] = block

HashOf(block) ==
    CHOOSE hash \in Hash :
        /\ hash.sequence \in DOMAIN hashFunction[hash.account]
        /\ hashFunction[hash.account][hash.sequence] = block

PublicKeyOf(block) ==
    IF block.type \in {"genesis", "open"}
    THEN block.account
    ELSE block.previous.account

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    IF HashIsDefined(block)
    THEN
        /\ newLastHash = HashOf(block)
        /\ UNCHANGED hashFunction
    ELSE
        LET publicKey == PublicKeyOf(block) IN
        /\ Len(hashFunction[publicKey]) < MaxHashCount
        /\ hashFunction' =
            [hashFunction EXCEPT
                ![publicKey] = Append(@, block)]
        /\ newLastHash =
            [account    |-> publicKey,
            sequence    |-> Len(hashFunction'[publicKey])]

TypeInvariant ==
    /\ hashFunction \in [PublicKey -> Seq(N!Block)]
    /\ N!TypeInvariant

SafetyInvariant ==
    /\ N!SafetyInvariant

Init ==
    /\ hashFunction = [key \in PublicKey |-> <<>>]
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

NanoView ==
    <<hashFunction, distributedLedger, received>>

=============================================================================