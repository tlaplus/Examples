-------------------------------- MODULE Nano --------------------------------
(***************************************************************************)
(* An outdated and not-ultimately-useful specification of the original     *)
(* protocol used by the Nano blockchain. Primarily interesting as an       *)
(* example of how to model hash functions and cryptographic signatures,    *)
(* and the difficulties in using finite modelchecking to analyze           *)
(* blockchain-like data structures or anything else that records action    *)
(* history in an ordered way.                                              *)
(***************************************************************************)

EXTENDS
    Naturals,
    Bags

CONSTANTS
    Hash,                   \* The set of all 256-bit Blake2b block hashes
    CalculateHash(_,_,_),   \* An action calculating the hash of a block
    PrivateKey,             \* The set of all Ed25519 private keys
    PublicKey,              \* The set of all Ed25519 public keys
    KeyPair,                \* The public key paired with each private key
    Node,                   \* The set of all nodes in the network
    GenesisBalance,         \* The total number of coins in the network
    Ownership               \* The private key owned by each node

VARIABLES
    lastHash,               \* The last calculated block hash
    distributedLedger,      \* The distributed ledger of confirmed blocks
    received                \* The blocks received but not yet validated

ASSUME
    /\ \A data, oldHash, newHash :
        /\ CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

-----------------------------------------------------------------------------

(***************************************************************************)
(* Functions to sign hashes with private key and validate signatures       *)
(* against public key.                                                     *)
(***************************************************************************)

SignHash(hash, privateKey) ==
    [data       |-> hash,
    signedWith  |-> privateKey]

ValidateSignature(signature, expectedPublicKey, expectedHash) ==
    LET publicKey == KeyPair[signature.signedWith] IN
    /\ publicKey = expectedPublicKey
    /\ signature.data = expectedHash

Signature ==
    [data       : Hash,
    signedWith  : PrivateKey]

(***************************************************************************)
(* Defines the set of protocol-conforming blocks.                          *)
(***************************************************************************)

AccountBalance == 0 .. GenesisBalance

GenesisBlock ==
    [type       : {"genesis"},
    account     : PublicKey,
    balance     : {GenesisBalance}]

SendBlock ==
    [previous   : Hash,
    balance     : AccountBalance,
    destination : PublicKey,
    type        : {"send"}]

OpenBlock ==
    [account    : PublicKey,
    source      : Hash,
    rep         : PublicKey,
    type        : {"open"}]

ReceiveBlock ==
    [previous   : Hash,
    source      : Hash,
    type        : {"receive"}]

ChangeRepBlock ==
    [previous   : Hash,
    rep         : PublicKey,
    type        : {"change"}]

Block ==
    GenesisBlock
    \cup SendBlock
    \cup OpenBlock
    \cup ReceiveBlock
    \cup ChangeRepBlock

SignedBlock ==
    [block      : Block,
    signature   : Signature]

NoBlock == CHOOSE b : b \notin SignedBlock

NoHash == CHOOSE h : h \notin Hash

Ledger == [Hash -> SignedBlock \cup {NoBlock}]

(***************************************************************************)
(* Utility functions to calculate block lattice properties.                *)
(***************************************************************************)

GenesisBlockExists ==
    /\ lastHash /= NoHash

IsAccountOpen(ledger, publicKey) ==
    /\ \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ signedBlock.block.type \in {"genesis", "open"}
        /\ signedBlock.block.account = publicKey

IsSendReceived(ledger, sourceHash) ==
    /\ \E hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ signedBlock.block.type \in {"open", "receive"}
        /\ signedBlock.block.source = sourceHash

RECURSIVE PublicKeyOf(_,_)
PublicKeyOf(ledger, blockHash) ==
    LET
      signedBlock == ledger[blockHash]
      block == signedBlock.block
    IN
    IF block.type \in {"genesis", "open"}
    THEN block.account
    ELSE PublicKeyOf(ledger, block.previous)

TopBlock(ledger, publicKey) ==
    CHOOSE hash \in Hash :
        LET signedBlock == ledger[hash] IN
        /\ signedBlock /= NoBlock
        /\ PublicKeyOf(ledger, hash) = publicKey
        /\ ~\E otherHash \in Hash :
            LET otherSignedBlock == ledger[otherHash] IN
            /\ otherSignedBlock /= NoBlock
            /\ otherSignedBlock.block.type \in {"send", "receive", "change"}
            /\ otherSignedBlock.block.previous = hash

RECURSIVE BalanceAt(_, _)
RECURSIVE ValueOfSendBlock(_, _)

BalanceAt(ledger, hash) ==
    LET
      signedBlock == ledger[hash]
      block == signedBlock.block
    IN
    CASE block.type = "open" -> ValueOfSendBlock(ledger, block.source)
    [] block.type = "send" -> block.balance
    [] block.type = "receive" ->
        BalanceAt(ledger, block.previous)
        + ValueOfSendBlock(ledger, block.source)
    [] block.type = "change" -> BalanceAt(ledger, block.previous)
    [] block.type = "genesis" -> block.balance

ValueOfSendBlock(ledger, hash) ==
    LET
      signedBlock == ledger[hash]
      block == signedBlock.block
    IN BalanceAt(ledger, block.previous) - block.balance
 
(***************************************************************************)
(* The type & safety invariants.                                           *)
(***************************************************************************)

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET SignedBlock]

CryptographicInvariant ==
    /\ \A node \in Node :
        LET ledger == distributedLedger[node] IN
        /\ \A hash \in Hash :
            LET signedBlock == ledger[hash] IN
            /\ signedBlock /= NoBlock =>
                LET publicKey == PublicKeyOf(ledger, hash) IN
                /\ ValidateSignature(
                    signedBlock.signature,
                    publicKey,
                    hash)

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN
    IF S = {}
    THEN 0
    ELSE
        LET e == CHOOSE x \in S : TRUE IN
        e + SumBag(B (-) SetToBag({e}))

BalanceInvariant ==
    /\ \A node \in Node :
        LET
          ledger == distributedLedger[node]
          openAccounts == {account \in PublicKey : IsAccountOpen(ledger, account)}
          topBlocks == {TopBlock(ledger, account) : account \in openAccounts}
          accountBalances ==
            LET ledgerBalanceAt(hash) == BalanceAt(ledger, hash) IN
            BagOfAll(ledgerBalanceAt, SetToBag(topBlocks))
        IN
        /\ GenesisBlockExists =>
            /\ SumBag(accountBalances) <= GenesisBalance

SafetyInvariant ==
    /\ CryptographicInvariant

(***************************************************************************)
(* Creates the genesis block.                                              *)
(***************************************************************************)

CreateGenesisBlock(privateKey) ==
    LET
      publicKey == KeyPair[privateKey]
      genesisBlock ==
        [type   |-> "genesis",
        account |-> publicKey,
        balance |-> GenesisBalance]
    IN
    /\ ~GenesisBlockExists
    /\ CalculateHash(genesisBlock, lastHash, lastHash')
    /\ distributedLedger' =
        LET signedGenesisBlock ==
            [block      |-> genesisBlock,
            signature   |-> SignHash(lastHash', privateKey)]
        IN
        [n \in Node |->
            [distributedLedger[n] EXCEPT
                ![lastHash'] =
                    signedGenesisBlock]]
    /\ UNCHANGED received

(***************************************************************************)
(* Creation, validation, and confirmation of open blocks. Checks include:  *)
(*  - The block is signed by the private key of the account being opened   *)
(*  - The node's ledger contains the referenced source block               *)
(*  - The source block is a send block to the account being opened         *)
(***************************************************************************)

ValidateOpenBlock(ledger, block) ==
    /\ block.type = "open"
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination = block.account

CreateOpenBlock(node) ==
    LET
      privateKey == Ownership[node]
      publicKey == KeyPair[privateKey]
      ledger == distributedLedger[node]
    IN
    /\ \E repPublicKey \in PublicKey :
        /\ \E srcHash \in Hash :
            LET newOpenBlock ==
                [account    |-> publicKey,
                source      |-> srcHash,
                rep         |-> repPublicKey,
                type        |-> "open"]
            IN
            /\ ValidateOpenBlock(ledger, newOpenBlock)
            /\ CalculateHash(newOpenBlock, lastHash, lastHash')
            /\ received' =
                LET signedOpenBlock ==
                    [block      |-> newOpenBlock,
                    signature   |-> SignHash(lastHash', privateKey)]
                IN
                [n \in Node |->
                    received[n] \cup {signedOpenBlock}]
            /\ UNCHANGED distributedLedger

ProcessOpenBlock(node, signedBlock) ==
    LET
      ledger == distributedLedger[node]
      block == signedBlock.block
    IN
    /\ ValidateOpenBlock(ledger, block)
    /\ ~IsAccountOpen(ledger, block.account)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(signedBlock.signature, block.account, lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT
            ![node][lastHash'] = signedBlock]

(***************************************************************************)
(* Creation, validation, and confirmation of send blocks. Checks include:  *)
(*  - The node's ledger contains the referenced previous block             *)
(*  - The block is signed by the account sourcing the funds                *)
(*  - The value sent is non-negative                                       *)
(***************************************************************************)

ValidateSendBlock(ledger, block) ==
    /\ block.type = "send"
    /\ ledger[block.previous] /= NoBlock
    /\ block.balance <= BalanceAt(ledger, block.previous)

CreateSendBlock(node) ==
    LET
      privateKey == Ownership[node]
      publicKey == KeyPair[privateKey]
      ledger == distributedLedger[node]
    IN
    /\ \E prevHash \in Hash :
        /\ ledger[prevHash] /= NoBlock
        /\ PublicKeyOf(ledger, prevHash) = publicKey
        /\ \E recipient \in PublicKey :
            /\ \E newBalance \in AccountBalance :
                LET newSendBlock ==
                    [previous   |-> prevHash,
                    balance     |-> newBalance,
                    destination |-> recipient,
                    type        |-> "send"]
                IN
                /\ ValidateSendBlock(ledger, newSendBlock)
                /\ CalculateHash(newSendBlock, lastHash, lastHash')
                /\ received' =
                    LET signedSendBlock ==
                        [block      |-> newSendBlock,
                        signature   |-> SignHash(lastHash', privateKey)]
                    IN
                    [n \in Node |->
                        received[n] \cup {signedSendBlock}]
                /\ UNCHANGED distributedLedger

ProcessSendBlock(node, signedBlock) ==
    LET
      ledger == distributedLedger[node]
      block == signedBlock.block
    IN
    /\ ValidateSendBlock(ledger, block)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(
        signedBlock.signature,
        PublicKeyOf(ledger, block.previous),
        lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT
            ![node][lastHash'] = signedBlock]

(***************************************************************************)
(* Creation, validation, & confirmation of receive blocks. Checks include: *)
(*  - The node's ledger contains the referenced previous & source blocks   *)
(*  - The block is signed by the account sourcing the funds                *)
(*  - The source block is a send block to the receive block's account      *)
(*  - The source block does not already have a corresponding receive/open  *)
(***************************************************************************)

ValidateReceiveBlock(ledger, block) ==
    /\ block.type = "receive"
    /\ ledger[block.previous] /= NoBlock
    /\ ledger[block.source] /= NoBlock
    /\ ledger[block.source].block.type = "send"
    /\ ledger[block.source].block.destination =
        PublicKeyOf(ledger, block.previous)

CreateReceiveBlock(node) ==
    LET
      privateKey == Ownership[node]
      publicKey == KeyPair[privateKey]
      ledger == distributedLedger[node]
    IN
    /\ \E prevHash \in Hash : 
        /\ ledger[prevHash] /= NoBlock
        /\ PublicKeyOf(ledger, prevHash) = publicKey
        /\ \E srcHash \in Hash :
            LET newRcvBlock ==
                [previous   |-> prevHash,
                source      |-> srcHash,
                type        |-> "receive"]
            IN
            /\ ValidateReceiveBlock(ledger, newRcvBlock)
            /\ CalculateHash(newRcvBlock, lastHash, lastHash')
            /\ received' =
                LET signedRcvBlock ==
                    [block      |-> newRcvBlock,
                    signature   |-> SignHash(lastHash', privateKey)]
                IN
                [n \in Node |->
                    received[n] \cup {signedRcvBlock}]
            /\ UNCHANGED distributedLedger

ProcessReceiveBlock(node, signedBlock) ==
    LET
      block == signedBlock.block
      ledger == distributedLedger[node]
    IN
    /\ ValidateReceiveBlock(ledger, block)
    /\ ~IsSendReceived(ledger, block.source)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(
        signedBlock.signature,
        PublicKeyOf(ledger, block.previous),
        lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT
            ![node][lastHash'] = signedBlock]

(***************************************************************************)
(* Creation, validation, & confirmation of change blocks. Checks include:  *)
(*  - The node's ledger contains the referenced previous block             *)
(*  - The block is signed by the correct account                           *)
(***************************************************************************)

ValidateChangeBlock(ledger, block) ==
    /\ block.type = "change"
    /\ ledger[block.previous] /= NoBlock

CreateChangeRepBlock(node) ==
    LET
      privateKey == Ownership[node]
      publicKey == KeyPair[privateKey]
      ledger == distributedLedger[node]
    IN
    /\ \E prevHash \in Hash :
        /\ ledger[prevHash] /= NoBlock
        /\ PublicKeyOf(ledger, prevHash) = publicKey
        /\ \E newRep \in PublicKey :
            LET newChangeRepBlock ==
                [previous   |-> prevHash,
                rep         |-> newRep,
                type        |-> "change"]
            IN
            /\ ValidateChangeBlock(ledger, newChangeRepBlock)
            /\ CalculateHash(newChangeRepBlock, lastHash, lastHash')
            /\ received' =
                LET signedChangeRepBlock ==
                    [block      |-> newChangeRepBlock,
                    signature   |-> SignHash(lastHash', privateKey)]
                IN
                [n \in Node |->
                    received[n] \cup {signedChangeRepBlock}]
            /\ UNCHANGED distributedLedger

ProcessChangeRepBlock(node, signedBlock) ==
    LET
      block == signedBlock.block
      ledger == distributedLedger[node]
    IN
    /\ ValidateChangeBlock(ledger, block)
    /\ CalculateHash(block, lastHash, lastHash')
    /\ ValidateSignature(
        signedBlock.signature,
        PublicKeyOf(ledger, block.previous),
        lastHash')
    /\ distributedLedger' =
        [distributedLedger EXCEPT
            ![node][lastHash'] = signedBlock]

(***************************************************************************)
(* Top-level actions.                                                      *)
(***************************************************************************)
CreateBlock(node) ==
    \/ CreateOpenBlock(node)
    \/ CreateSendBlock(node)
    \/ CreateReceiveBlock(node)
    \/ CreateChangeRepBlock(node)

ProcessBlock(node) ==
    /\ \E block \in received[node] :
        /\  \/ ProcessOpenBlock(node, block)
            \/ ProcessSendBlock(node, block)
            \/ ProcessReceiveBlock(node, block)
            \/ ProcessChangeRepBlock(node, block)
        /\ received' = [received EXCEPT ![node] = @ \ {block}]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

Next ==
    \/ \E account \in PrivateKey : CreateGenesisBlock(account)
    \/ \E node \in Node : CreateBlock(node)
    \/ \E node \in Node : ProcessBlock(node)

Spec ==
    /\ Init
    /\ [][Next]_<<lastHash, distributedLedger, received>>

THEOREM Safety == Spec => TypeInvariant /\ SafetyInvariant

=============================================================================

