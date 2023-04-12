--------------------------- MODULE Paxos -----------------------------
(*
    This is a specification of the Paxos protocol without explicit leaders or learners.
*)

EXTENDS TLC, Naturals, FiniteSets, Integers

CONSTANTS any, none, Replicas, Values, Ballots, Quorums

VARIABLES messages \* Set of all messages sent.
VARIABLES decision \* Decided value of an acceptor.
VARIABLES maxBallot \* Maximum ballot an acceptor has seen.
VARIABLES maxVBallot \* Maximum ballot an acceptor has accepted.
VARIABLES maxValue \* Maximum value an acceptor has accepted.

\* Set of all possible messages.
P1aMessage == [type : {"P1a"},
               ballot : Ballots \ {0}]
P1bMessage == [type : {"P1b"},
               ballot : Ballots,
               acceptor : Replicas,
               maxVBallot : Ballots,
               maxValue : Values \union {none}] \* (maxVBallot = 0) <=> (maxValue = none)
P2aMessage == [type : {"P2a"},
               ballot : Ballots,
               value : Values \union {any}]
P2bMessage == [type : {"P2b"},
               ballot : Ballots,
               acceptor : Replicas,
               value : Values]
Message == P1aMessage \union P1bMessage \union P2aMessage \union P2bMessage

ASSUME PaxosAssume ==
    /\ IsFiniteSet(Replicas)
    /\ any \notin Values \union {none}
    /\ none \notin Values \union {any}
    /\ Ballots \subseteq Nat /\ 0 \in Ballots
    /\ \A q \in Quorums : q \subseteq Replicas
    /\ \A q \in Quorums : Cardinality(Replicas) \div 2 < Cardinality(q)
    /\ \A q, r \in Quorums : q \intersect r # {}

p1aMessages == {m \in messages : m.type = "P1a"} \* Set of all P1a messages sent.
p1bMessages == {m \in messages : m.type = "P1b"} \* Set of all P1b messages sent.
p2aMessages == {m \in messages : m.type = "P2a"} \* Set of all P2a messages sent.
p2bMessages == {m \in messages : m.type = "P2b"} \* Set of all P2b messages sent.

ForcedValue(M) == (CHOOSE m \in M : \A n \in M : n.maxVBallot <= m.maxVBallot).maxValue

SendMessage(m) == messages' = messages \union {m}

(*
    Phase 1a:

    A proposer creates a message, which we call a "Prepare", identified with a ballot number b.
    Note that b is not the value to be proposed and maybe agreed on, but just a number
    which uniquely identifies this initial message by the proposer (to be sent to the acceptors).

    While ballot number b must be greater than any ballot number used in any of the previous Prepare messages by this proposer,
    since the system is asynchronous and messages may be delayed and arrive out-of-order, there is no need to explicitly model this.

    Then, it sends the Prepare message containing b to at least a quorum of acceptors.
    Note that the Prepare message only contains the ballot number b (that is, it does not have to contain the proposed value).

    A Proposer should not initiate Paxos if it cannot communicate with at least a Quorum of Acceptors.

    Some implementations may include the identity of the proposer, but that is omitted in this specification.
    Because while it is possible for multiple proposers to send a Prepare message with the same ballot number,
    only one of them can possibly receive a quorum of Promise replies. Thus, it is impossible for more than one proposer
    to have the same ballot number in Phase 2a.
*)
PaxosPrepare ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in Ballots \ {0} :
        SendMessage([type |-> "P1a",
                     ballot |-> b])

(*
    Phase 1b:

    Any of the acceptors waits for a Prepare message from any of the proposers.
    If an acceptor receives a Prepare message, the acceptor must look at the ballot number b of the just received Prepare message.

    There are two cases:

        1. If b is higher than every previous proposal number received, from any of the proposers, by the acceptor,
           then the acceptor must return a message, which we call a "Promise", to the proposer, to ignore all future
           proposals having a ballot less than b. If the acceptor accepted a proposal at some point in the past, it
           must include the previous proposal number and the corresponding accepted value in its response to the proposer.

        2. Otherwise the acceptor can ignore the received proposal. It does not have to answer in this case for Paxos to work.
*)
PaxosPromise ==
    /\ UNCHANGED<<decision, maxVBallot, maxValue>>
    /\ \E a \in Replicas, m \in p1aMessages :
        /\ maxBallot[a] < m.ballot
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ SendMessage([type |-> "P1b",
                        ballot |-> m.ballot,
                        acceptor |-> a,
                        maxVBallot |-> maxVBallot[a],
                        maxValue |-> maxValue[a]])

(*
    Phase 2a:

    If a proposer receives Promises from a quorum of acceptors, it needs to set a value v to its proposal.
    If any acceptors had previously accepted any proposal, then they'll have sent their values to the proposer,
    who now must set the value of its proposal, v, to the value associated with the highest proposal ballot reported by
    the acceptors, let's call it z. If none of the acceptors had accepted a proposal up to this point, then the proposer
    may choose the value it originally wanted to propose, say x.

    The proposer sends an Accept message, (b, v), to a quorum of acceptors with the chosen value for its proposal, v, and the ballot
    number b (which is the same as the number contained in the Prepare message previously sent to the acceptors). So, the Accept message
    is either (b, v=z) or, in case none of the Acceptors previously accepted a value, (b, v=x).

    This Accept message should be interpreted as a "request", as in "Accept this proposal, please!".
*)
PaxosAccept ==
    /\ UNCHANGED<<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in Ballots, q \in Quorums, v \in Values :
        /\ \A m \in p2aMessages : ~(m.ballot = b)
        /\ LET M == {m \in p1bMessages : m.ballot = b /\ m.acceptor \in q}
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ \/ \A m \in M : m.maxValue = none
                 \/ v = ForcedValue(M)
              /\ SendMessage([type |-> "P2a",
                              ballot |-> b,
                              value |-> v])

(*
    Phase 2b:

    If an acceptor receives an Accept message, (b, v), from a proposer, it must accept it if and only if it has not already
    promised (in Phase 1b of the Paxos protocol) to only consider proposals having a ballot greater than b.

    If the acceptor has not already promised (in Phase 1b) to only consider proposals having a ballot greater than b,
    it should register the value v (of the just received Accept message) as the accepted value (of the protocol), and send
    an Accepted message to the proposer and every acceptor.

    Else, it can ignore the Accept message or request.
*)
PaxosAccepted ==
    /\ UNCHANGED<<decision>>
    /\ \E a \in Replicas, m \in p2aMessages :
        /\ m.value \in Values
        /\ maxBallot[a] <= m.ballot
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = m.value]
        /\ SendMessage([type |-> "P2b",
                        ballot |-> m.ballot,
                        acceptor |-> a,
                        value |-> m.value])

(*
    Consensus is achieved when a majority of acceptors accept the same ballot number (rather than the same value).
    Because each ballot is unique to a proposer and only one value may be proposed per ballot, all acceptors
    that accept the same ballot thereby accept the same value.

    There is no need to model the variable decision for every acceptor. In this specification, the variable decision
    represents the decision of any acceptor, can its value may potentially be changed multiple times. Instead, we use
    the consistency safety property to proof that the decision for every acceptor is the same.
*)
PaxosDecide ==
    /\ UNCHANGED<<messages, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in Ballots, q \in Quorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : decision' = m.value

PaxosTypeOK == /\ messages \subseteq Message
               /\ decision \in Values \union {none}
               /\ maxBallot \in [Replicas -> Ballots]
               /\ maxVBallot \in [Replicas -> Ballots]
               /\ maxValue \in [Replicas -> Values \union {none}]

PaxosInit == /\ messages = {}
             /\ decision = none
             /\ maxBallot = [r \in Replicas |-> 0]
             /\ maxVBallot = [r \in Replicas |-> 0]
             /\ maxValue = [r \in Replicas |-> none]

PaxosNext == \/ PaxosPrepare
             \/ PaxosPromise
             \/ PaxosAccept
             \/ PaxosAccepted
             \/ PaxosDecide

PaxosSpec == /\ PaxosInit
             /\ [][PaxosNext]_<<messages, decision, maxBallot, maxVBallot, maxValue>>
             /\ SF_<<messages, decision, maxBallot, maxVBallot, maxValue>>(PaxosDecide)

\* Non-triviality safety property: Only proposed values can be learnt.
PaxosNontriviality ==
    /\ \/ decision = none
       \/ \E m \in p2aMessages : m.value = decision
    /\ \A m \in p1bMessages : /\ m.maxValue \in Values \/ 0 = m.maxVBallot
                              /\ m.maxValue = none \/ 0 < m.maxVBallot

\* Consistency safety property: At most 1 value can be learnt.
PaxosConsistency == [][decision = none]_<<decision>>

(*
    From Wikipedia:

    Note that Paxos is not guaranteed to terminate, and thus does not
    have the liveness property. This is supported by the Fischer Lynch Paterson
    impossibility result (FLP) which states that a consistency protocol can
    only have two of safety, liveness, and fault tolerance.

    As Paxos's point is to ensure fault tolerance and it guarantees safety, it
    cannot also guarantee liveness. 
*)
PaxosLiveness == FALSE

\* Define symmetry for faster computations.
PaxosSymmetry == Permutations(Values) \union Permutations(Replicas)

===============================================================