------------------------- MODULE NanoMCSingleChain -------------------------

EXTENDS
    Naturals,
    Sequences

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

-----------------------------------------------------------------------------

Hash == 1 .. MaxHashCount

UndefinedHashesExist ==
    Len(hashFunction) < MaxHashCount

HashIsDefined(block) ==
    /\ \E h \in DOMAIN hashFunction : hashFunction[h] = block

HashOf(block) ==
    CHOOSE h \in DOMAIN hashFunction : hashFunction[h] = block

CalculateHashImpl(block, oldLastHash, newLastHash) ==
    IF HashIsDefined(block)
    THEN
        /\ newLastHash = HashOf(block)
        /\ UNCHANGED hashFunction
    ELSE
        /\ UndefinedHashesExist
        /\ hashFunction' = Append(hashFunction, block)
        /\ newLastHash = Len(hashFunction')

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

TypeInvariant ==
    /\ hashFunction \in Seq(N!Block)
    /\ N!TypeInvariant

SafetyInvariant ==
    /\ N!SafetyInvariant

Init ==
    /\ hashFunction = <<>>
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
        
=============================================================================