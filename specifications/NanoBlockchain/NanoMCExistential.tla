------------------------- MODULE NanoMCExistential -------------------------

EXTENDS
    Naturals,
    Sequences

CONSTANTS
    CalculateHash(_,_,_),
    Hash,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance

VARIABLES
    hashFunction,
    lastHash,
    distributedLedger,
    received

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

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    IF \E hash \in Hash : hashFunction[hash] = block
    THEN
        /\ newLastHash = CHOOSE hash \in Hash : hashFunction[hash] = block
        /\ UNCHANGED hashFunction
    ELSE
        /\ \E hash \in Hash :
            /\ hashFunction[hash] = N!NoBlock
            /\ hashFunction' = [hashFunction EXCEPT ![hash] = block]
            /\ newLastHash = hash

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
    IF \A hash \in Hash : hashFunction[hash] /= N!NoBlock
    THEN StutterWhenHashesDepleted
    ELSE N!Next

=============================================================================