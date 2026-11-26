(********************************************************************************)
(* This specification models MultiPaxos with leader leases. A leader holding    *)
(* leases from a majority of replicas can serve linearizable reads locally      *)
(* after committing recovered writes. The model covers lease acquisition,       *)
(* renewal, revocation, and expiration, including interactions with leader      *)
(* changes and replica failures.                                                *)
(*                                                                              *)
(* Algorithm reference:                                                         *)
(* Tushar D. Chandra, Robert Griesemer, and Joshua Redstone. 2007.              *)
(* Paxos made live: an engineering perspective. PODC '07, ACM, pp. 398-407.     *)
(* https://doi.org/10.1145/1281100.1281103                                      *)
(********************************************************************************)

---- MODULE MultiPaxos ----
EXTENDS FiniteSets, Sequences, Integers, TLC, Functions

(*******************************)
(* Model inputs & assumptions. *)
(*******************************)
CONSTANT Replicas,       \* symmetric set of server nodes
         Writes,         \* symmetric set of write commands (each w/ unique value)
         Reads,          \* symmetric set of read commands
         TGuard,         \* lease guard phase window length (in abstract ticks)
         TLease          \* lease renewal extend window length (in abstract ticks)

ReplicasAssumption == /\ IsFiniteSet(Replicas)
                      /\ Replicas # {}
                      /\ "none" \notin Replicas

Population == Cardinality(Replicas)

MajorityNum == (Population \div 2) + 1

ReadsWritesAssumption == /\ IsFiniteSet(Reads)
                         /\ IsFiniteSet(Writes)
                         /\ Writes # {}
                         /\ "nil" \notin Reads
                         /\ "nil" \notin Writes
                         /\ Reads \cap Writes = {}

TimeWindowsAssumption == /\ TGuard \in Nat \ {0}
                         /\ TLease \in Nat \ {0}

ASSUME /\ ReplicasAssumption
       /\ ReadsWritesAssumption
       /\ TimeWindowsAssumption

----------

(********************************)
(* Useful constants & typedefs. *)
(********************************)
Commands == Writes \cup Reads

NumWrites == Cardinality(Writes)

NumReads == Cardinality(Reads)

NumCommands == Cardinality(Commands)

\* Client observable events.
ClientEvents ==      [type: {"Req"}, cmd: Commands]
                \cup [type: {"Ack"}, cmd: Commands,
                                     val: {"nil"} \cup Writes]

ReqEvent(c) == [type |-> "Req", cmd |-> c]

AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]
                        \* for a write command, val is the old value

InitPending ==    (CHOOSE ws \in [1..Cardinality(Writes) -> Writes]
                        : IsInjective(ws))
               \o (CHOOSE rs \in [1..Cardinality(Reads) -> Reads]
                        : IsInjective(rs))
                    \* justification for CHOOSE: there is no identity associated
                    \* with each individual write/read command; we just need to
                    \* name any permutation of them to get started

\* Server-side consensus constants & states.
Ballots == Nat \ {0}

Slots == 1..NumWrites

InfinitySlot == NumWrites + 1
                    \* sentinel "infinitely-high" slot for dummy defaults

Statuses == {"Preparing", "Accepting", "Committed"}

InstStates == [status: {"Empty"} \cup Statuses,
               write: {"nil"} \cup Writes,
               voted: [bal: {0} \cup Ballots,
                       write: {"nil"} \cup Writes]]

NullInst == [status |-> "Empty",
             write |-> "nil",
             voted |-> [bal |-> 0, write |-> "nil"]]

\* Lease-side constants & typedefs.
Times == Nat \ {0}
ExpireTimes == Nat
                \* stored expiration / guard deadlines; 0 is the "null" time

SeqNums == Nat
            \* per-pair monotone seq nums on lease messages for dedup

GrantorStatuses == {"None", "Guarding", "Renewing", "Revoking"}
GranteeStatuses == {"None", "Guarded", "Renewed"}

GrantorState == [status: GrantorStatuses,
                 guardExpire: ExpireTimes,
                 leaseExpire: ExpireTimes,
                 bal: {0} \cup Ballots,
                 seq: SeqNums]

GranteeState == [status: GranteeStatuses,
                 guardExpire: ExpireTimes,
                 leaseExpire: ExpireTimes,
                 bal: {0} \cup Ballots,
                 seq: SeqNums]

NullGrantorState == [status |-> "None",
                     guardExpire |-> 0,
                     leaseExpire |-> 0,
                     bal |-> 0,
                     seq |-> 0]

NullGranteeState == [status |-> "None",
                     guardExpire |-> 0,
                     leaseExpire |-> 0,
                     bal |-> 0,
                     seq |-> 0]

\* Merged per-node state: consensus fields + lease fields.
NodeStates == [leader: {"none"} \cup Replicas,
               commitUpTo: {0} \cup Slots,
               commitPrev: {0} \cup Slots,
               balPrepared: {0} \cup Ballots,
               balMaxKnown: {0} \cup Ballots,
               insts: [Slots -> InstStates],
               asGrantor: [Replicas -> GrantorState],
               asGrantee: [Replicas -> GranteeState]]

NullNode == [leader |-> "none",
             commitUpTo |-> 0,
             commitPrev |-> 0,
             balPrepared |-> 0,
             balMaxKnown |-> 0,
             insts |-> [s \in Slots |-> NullInst],
             asGrantor |-> [p \in Replicas |-> NullGrantorState],
             asGrantee |-> [f \in Replicas |-> NullGranteeState]]
                \* commitPrev is the last slot which might have been
                \* committed by an old leader; a newly prepared leader
                \* can safely serve reads locally only after its log has
                \* been committed up to this slot
                \*
                \* asGrantor[p] is the grantor-side lease state & timers
                \* toward grantee p; asGrantee[f] is the grantee-side
                \* state toward grantor f

FirstEmptySlot(insts) ==
    IF \A s \in Slots: insts[s].status # "Empty"
        THEN InfinitySlot
        ELSE CHOOSE s \in Slots:
                /\ insts[s].status = "Empty"
                /\ \A t \in 1..(s - 1): insts[t].status # "Empty"
                \* justification for CHOOSE: the ELSE branch guarantees an
                \* empty slot exists; using CHOOSE to name it

\* Service-internal consensus messages.
PrepareMsgs == [type: {"Prepare"}, src: Replicas, bal: Ballots]

PrepareMsg(r, b) == [type |-> "Prepare", src |-> r, bal |-> b]

InstsVotes == [Slots -> [bal: {0} \cup Ballots, write: {"nil"} \cup Writes]]

VotesByNode(n) == [s \in Slots |-> n.insts[s].voted]

PrepareReplyMsgs == [type: {"PrepareReply"}, src: Replicas,
                                             bal: Ballots,
                                             votes: InstsVotes]

PrepareReplyMsg(r, b, iv) == [type |-> "PrepareReply", src |-> r,
                                                       bal |-> b,
                                                       votes |-> iv]

PeakVotedWrite(prs, s) ==
    IF \A pr \in prs: pr.votes[s].bal = 0
        THEN "nil"
        ELSE LET ppr ==
                    CHOOSE ppr \in prs:
                        \A pr \in prs: pr.votes[s].bal =< ppr.votes[s].bal
             IN  ppr.votes[s].write
                \* justification for CHOOSE: the ELSE branch guarantees a
                \* non-empty finite reply set, therefore a max ballot exists;
                \* using CHOOSE to name a reply with that max ballot

LastTouchedSlot(prs) ==
    IF \A s \in Slots: PeakVotedWrite(prs, s) = "nil"
        THEN 0
        ELSE CHOOSE s \in Slots:
                /\ PeakVotedWrite(prs, s) # "nil"
                /\ \A t \in (s + 1)..NumWrites: PeakVotedWrite(prs, t) = "nil"
                \* justification for CHOOSE: the ELSE branch guarantees a
                \* slot with non-nil PeakVotedWrite exists; using CHOOSE to
                \* name the highest slot among them

AcceptMsgs == [type: {"Accept"}, src: Replicas,
                                 bal: Ballots,
                                 slot: Slots,
                                 write: Writes]

AcceptMsg(r, b, s, c) == [type |-> "Accept", src |-> r,
                                             bal |-> b,
                                             slot |-> s,
                                             write |-> c]

AcceptReplyMsgs == [type: {"AcceptReply"}, src: Replicas,
                                           bal: Ballots,
                                           slot: Slots]

AcceptReplyMsg(r, b, s) == [type |-> "AcceptReply", src |-> r,
                                                    bal |-> b,
                                                    slot |-> s]

CommitNoticeMsgs == [type: {"CommitNotice"}, upto: Slots]

CommitNoticeMsg(u) == [type |-> "CommitNotice", upto |-> u]

\* Lease protocol messages. All carry ballot and per-pair seq num.
GuardMsgs == [type: {"Guard"}, grantor: Replicas,
                               grantee: Replicas,
                               bal: Ballots,
                               seq: SeqNums]

GuardMsg(f, p, b, s) == [type |-> "Guard", grantor |-> f,
                                           grantee |-> p,
                                           bal |-> b,
                                           seq |-> s]

GuardReplyMsgs == [type: {"GuardReply"}, grantee: Replicas,
                                         grantor: Replicas,
                                         bal: Ballots,
                                         seq: SeqNums]

GuardReplyMsg(p, f, b, s) == [type |-> "GuardReply", grantee |-> p,
                                                     grantor |-> f,
                                                     bal |-> b,
                                                     seq |-> s]

RenewMsgs == [type: {"Renew"}, grantor: Replicas,
                               grantee: Replicas,
                               bal: Ballots,
                               seq: SeqNums]

RenewMsg(f, p, b, s) == [type |-> "Renew", grantor |-> f,
                                           grantee |-> p,
                                           bal |-> b,
                                           seq |-> s]

RenewReplyMsgs == [type: {"RenewReply"}, grantee: Replicas,
                                         grantor: Replicas,
                                         bal: Ballots,
                                         seq: SeqNums]

RenewReplyMsg(p, f, b, s) == [type |-> "RenewReply", grantee |-> p,
                                                     grantor |-> f,
                                                     bal |-> b,
                                                     seq |-> s]

RevokeMsgs == [type: {"Revoke"}, grantor: Replicas,
                                 grantee: Replicas,
                                 bal: Ballots,
                                 seq: SeqNums]

RevokeMsg(f, p, b, s) == [type |-> "Revoke", grantor |-> f,
                                             grantee |-> p,
                                             bal |-> b,
                                             seq |-> s]

RevokeReplyMsgs == [type: {"RevokeReply"}, grantee: Replicas,
                                           grantor: Replicas,
                                           bal: Ballots,
                                           seq: SeqNums]

RevokeReplyMsg(p, f, b, s) == [type |-> "RevokeReply", grantee |-> p,
                                                       grantor |-> f,
                                                       bal |-> b,
                                                       seq |-> s]

Messages ==      PrepareMsgs
            \cup PrepareReplyMsgs
            \cup AcceptMsgs
            \cup AcceptReplyMsgs
            \cup CommitNoticeMsgs
            \cup GuardMsgs
            \cup GuardReplyMsgs
            \cup RenewMsgs
            \cup RenewReplyMsgs
            \cup RevokeMsgs
            \cup RevokeReplyMsgs

----------

(******************************)
(* Main algorithm in PlusCal. *)
(******************************)
(*--algorithm MultiPaxos

variable msgs = {},                             \* messages in the network
         node = [r \in Replicas |-> NullNode],  \* replica merged state
         pending = InitPending,                 \* sequence of pending reqs
         observed = <<>>,                       \* client observed events
         crashed = [r \in Replicas |-> FALSE],  \* replica crashed flag
         time = [r \in Replicas |-> 1];         \* per-node monotone clock
            \* for simplicity, this spec initializes all nodes' clocks to the
            \* same value of 1; this is not a requirement of leasing -- nodes
            \* always reference their own clock and they don't need to align on
            \* the absolute timestamps (i.e., clock skew is fine)

define
    \* A lease from grantee p's perspective is "active" iff p's asGrantee[f]
    \* is in Renewed status and un-expired at ballot b.
    FGrantsPWithBal(f, p, b) == /\ node[p].asGrantee[f].status = "Renewed"
                                /\ node[p].asGrantee[f].leaseExpire > time[p]
                                /\ node[p].asGrantee[f].bal = b

    \* True if a node r thinks of itself as a stable leader.
    ThinkAmLeader(r) ==
        /\ node[r].leader = r
        /\ node[r].balPrepared = node[r].balMaxKnown
        /\ Cardinality({f \in Replicas:
                        FGrantsPWithBal(f, r, node[r].balMaxKnown)})
           >= MajorityNum

    \* When node r's ballot rises to nb, any live outgoing grant at an older
    \* ballot are revoked: Guarding grants reset locally, Renewing grants move
    \* to Revoking with seq num bumped. Expired grants are untouched (cleared
    \* later by TimeTick).
    RevokeStaleAsGrantor(r, nb) ==
        [p \in Replicas |->
            LET g == node[r].asGrantor[p]
            IN  IF      /\ g.bal < nb
                        /\ g.status = "Guarding"
                        /\ g.guardExpire > time[r]
                    THEN [NullGrantorState EXCEPT !.seq = g.seq]
                ELSE IF /\ g.bal < nb
                        /\ g.status = "Renewing"
                        /\ g.leaseExpire > time[r]
                    THEN [g EXCEPT !.status = "Revoking", !.seq = g.seq + 1]
                ELSE g]

    \* Revoke messages to emit alongside RevokeStaleAsGrantor(r, nb). Seq num
    \* matches the bumped seq num in the Revoking state above.
    RevokeStaleSendMsgs(r, nb) ==
        {RevokeMsg(r, p, nb, node[r].asGrantor[p].seq + 1):
         p \in {p \in Replicas: /\ node[r].asGrantor[p].bal < nb
                                /\ node[r].asGrantor[p].status = "Renewing"
                                /\ node[r].asGrantor[p].leaseExpire > time[r]}}

    \* Miscellaneous model checking helpers:
    AppendObserved(seq) ==
        LET filter(e) == e \notin Range(observed)
        IN  observed \o SelectSeq(seq, filter)

    UnseenPending(r) ==
        LET filter(c) == \A s \in Slots: node[r].insts[s].write # c
        IN  SelectSeq(pending, filter)

    RemovePending(cmd) ==
        LET filter(c) == c # cmd
        IN  SelectSeq(pending, filter)

    reqsMade == {e.cmd: e \in {e \in Range(observed): e.type = "Req"}}

    acksRecv == {e.cmd: e \in {e \in Range(observed): e.type = "Ack"}}

    terminated == /\ Len(pending) = 0
                  /\ Cardinality(reqsMade) = NumCommands
                  /\ Cardinality(acksRecv) = NumCommands

    NodeFailuresOn == TRUE  \* replicas may crash at any time
end define;

\* Send a set of messages helper.
macro Send(set) begin
    msgs := msgs \cup set;
end macro;

\* Observe client events helper.
macro Observe(seq) begin
    observed := AppendObserved(seq);
end macro;

\* Resolve a pending command helper.
macro Resolve(c) begin
    pending := RemovePending(c);
end macro;

\* Someone steps up as leader and sends Prepare message to followers.
\* Also revokes any stale outgoing lease grants: Guarding ones are reset
\* locally; Renewing ones transition to Revoking and send Revoke to
\* respective grantees.
macro BecomeLeader(r) begin
    \* if I'm not a leader
    await node[r].leader # r;
    \* pick a greater ballot number
    with b \in Ballots do
        await /\ b > node[r].balMaxKnown
              /\ ~\E m \in msgs: (m.type = "Prepare") /\ (m.bal = b);
                    \* W.L.O.G., using this clause to model that ballot
                    \* numbers from different proposers be unique
        \* update states and restart Prepare phase for in-progress instances;
        \* also revoke any stale outgoing lease grants
        node[r].leader := r ||
        node[r].balPrepared := 0 ||
        node[r].balMaxKnown := b ||
        node[r].insts :=
            [s \in Slots |->
                [node[r].insts[s]
                    EXCEPT !.status = IF @ = "Accepting"
                                        THEN "Preparing"
                                        ELSE @]] ||
        node[r].asGrantor := RevokeStaleAsGrantor(r, b);
        \* broadcast Prepare and reply to myself instantly; also send Revokes
        \* for the just-Revoking grants
        Send(      {PrepareMsg(r, b),
                    PrepareReplyMsg(r, b, VotesByNode(node[r]))}
              \cup RevokeStaleSendMsgs(r, b));
    end with;
end macro;

\* Replica replies to a Prepare message. Also revokes any stale outgoing lease
\* grants the same way as BecomeLeader does.
macro HandlePrepare(r) begin
    \* if receiving a Prepare message with larger ballot than ever seen
    with m \in msgs do
        await /\ m.type = "Prepare"
              /\ m.bal > node[r].balMaxKnown;
        \* update consensus states; also revoke any stale outgoing lease grants
        node[r].leader := m.src ||
        node[r].balMaxKnown := m.bal ||
        node[r].insts :=
            [s \in Slots |->
                [node[r].insts[s]
                    EXCEPT !.status = IF @ = "Accepting"
                                        THEN "Preparing"
                                        ELSE @]] ||
        node[r].asGrantor := RevokeStaleAsGrantor(r, m.bal);
        \* send back PrepareReply with my voted list; also send Revokes for
        \* the just-Revoking grants
        Send(      {PrepareReplyMsg(r, m.bal, VotesByNode(node[r]))}
              \cup RevokeStaleSendMsgs(r, m.bal));
    end with;
end macro;

\* Leader gathers PrepareReply messages until condition met, then marks
\* the corresponding ballot as prepared and saves highest voted commands.
macro HandlePrepareReplies(r) begin
    \* if I'm waiting for PrepareReplies
    await /\ node[r].leader = r
          /\ node[r].balPrepared = 0;
    \* when there are enough number of PrepareReplies of desired ballot
    with prs = {m \in msgs: /\ m.type = "PrepareReply"
                            /\ m.bal = node[r].balMaxKnown}
    do
        await Cardinality(prs) >= MajorityNum;
        with prsGot \in {prsGot \in SUBSET prs:
                         Cardinality(prsGot) >= MajorityNum},
             lts = LastTouchedSlot(prsGot)
        do
            \* marks this ballot as prepared and saves highest voted command
            \* in each slot if any
            node[r].balPrepared := node[r].balMaxKnown ||
            node[r].insts :=
                [s \in Slots |->
                    LET pvw == PeakVotedWrite(prsGot, s)
                        adopted == \/ node[r].insts[s].status = "Preparing"
                                   \/ /\ node[r].insts[s].status = "Empty"
                                      /\ pvw # "nil"
                    IN  [node[r].insts[s]
                            EXCEPT !.status = IF adopted
                                                THEN "Accepting"
                                                ELSE @,
                                   !.write  = pvw,
                                   !.voted  = IF adopted
                                                THEN [bal |-> node[r].balMaxKnown,
                                                      write |-> pvw]
                                                ELSE @]] ||
            node[r].commitPrev := lts;
            \* send Accept messages for in-progress instances and reply to
            \* myself instantly
            Send(UNION
                 {{AcceptMsg(r, node[r].balPrepared, s, node[r].insts[s].write),
                   AcceptReplyMsg(r, node[r].balPrepared, s)}:
                  s \in {s \in Slots: node[r].insts[s].status = "Accepting"}});
        end with;
    end with;
end macro;

\* A prepared leader takes a new write request into the next empty slot.
macro TakeNewWriteRequest(r) begin
    \* if I'm a prepared leader and there's pending write request
    await /\ ThinkAmLeader(r)
          /\ \E s \in Slots: node[r].insts[s].status = "Empty"
          /\ Len(UnseenPending(r)) > 0
          /\ Head(UnseenPending(r)) \in Writes;
    \* find the next empty slot and pick a pending request
    with s = FirstEmptySlot(node[r].insts),
         c = Head(UnseenPending(r))
                \* W.L.O.G., only pick a command not seen in current
                \* prepared log to have smaller state space
    do
        \* update slot status and voted
        node[r].insts[s].status := "Accepting" ||
        node[r].insts[s].write := c ||
        node[r].insts[s].voted.bal := node[r].balPrepared ||
        node[r].insts[s].voted.write := c;
        \* broadcast Accept and reply to myself instantly
        Send({AcceptMsg(r, node[r].balPrepared, s, c),
              AcceptReplyMsg(r, node[r].balPrepared, s)});
        \* append to observed events sequence if haven't yet
        Observe(<<ReqEvent(c)>>);
    end with;
end macro;

\* Replica replies to an Accept message. If the Accept's ballot is higher than
\* what we've known, also revokes any stale outgoing lease grants.
macro HandleAccept(r) begin
    \* if receiving an unreplied Accept message with valid ballot
    with m \in msgs do
        await /\ m.type = "Accept"
              /\ m.bal >= node[r].balMaxKnown
              /\ m.bal >= node[r].insts[m.slot].voted.bal;
        \* update node states and corresponding instance's states; also
        \* revoke any stale outgoing lease grants
        node[r].leader := m.src ||
        node[r].balMaxKnown := m.bal ||
        node[r].insts[m.slot].status := "Accepting" ||
        node[r].insts[m.slot].write := m.write ||
        node[r].insts[m.slot].voted.bal := m.bal ||
        node[r].insts[m.slot].voted.write := m.write ||
        node[r].asGrantor := RevokeStaleAsGrantor(r, m.bal);
        \* send back AcceptReply; also send Revokes for the just-Revoking grants
        Send(      {AcceptReplyMsg(r, m.bal, m.slot)}
              \cup RevokeStaleSendMsgs(r, m.bal));
    end with;
end macro;

\* Leader gathers AcceptReply messages for a slot until condition met, then
\* marks the slot as committed and acknowledges the client.
macro HandleAcceptReplies(r) begin
    \* if I'm a prepared leader
    await /\ ThinkAmLeader(r)
          /\ node[r].commitUpTo < NumWrites
          /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting";
                \* W.L.O.G., only enabling the next slot after commitUpTo
    \* for this slot, when there are enough number of AcceptReplies
    with s = node[r].commitUpTo + 1,
         c = node[r].insts[s].write,
         ps = s - 1,
         v = IF ps = 0 THEN "nil" ELSE node[r].insts[ps].write,
         ars = {m \in msgs: /\ m.type = "AcceptReply"
                            /\ m.slot = s
                            /\ m.bal = node[r].balPrepared}
    do
        await Cardinality(ars) >= MajorityNum;
        with arsGot \in {arsGot \in SUBSET ars:
                         Cardinality(arsGot) >= MajorityNum}
        do
            \* marks this slot as committed and apply command
            node[r].insts[s].status := "Committed" ||
            node[r].commitUpTo := s;
            \* append to observed events sequence if haven't yet, and remove
            \* the command from pending
            Observe(<<AckEvent(c, v)>>);
            Resolve(c);
            \* broadcast CommitNotice to followers
            Send({CommitNoticeMsg(s)});
        end with;
    end with;
end macro;

\* Replica receives new commit notification.
macro HandleCommitNotice(r) begin
    \* if I'm a follower waiting on CommitNotice
    await /\ node[r].leader # r
          /\ node[r].commitUpTo < NumWrites
          /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting";
    \* for this slot, when there's a CommitNotice message
    with s = node[r].commitUpTo + 1,
         c = node[r].insts[s].write,
         m \in msgs
    do
        await /\ m.type = "CommitNotice"
              /\ m.upto = s;
        \* marks this slot as committed and apply command
        node[r].insts[s].status := "Committed" ||
        node[r].commitUpTo := s;
    end with;
end macro;

\* Assuming using leader leases, a prepared leader takes a new read request
\* and serves it locally. ThinkAmLeader gates this action.
macro TakeNewReadRequest(r) begin
    \* if I'm a prepared and recovered leader that has committed all slots
    \* of old ballots, and there's pending read request
    await /\ ThinkAmLeader(r)
          /\ node[r].commitUpTo >= node[r].commitPrev
          /\ Len(UnseenPending(r)) > 0
          /\ Head(UnseenPending(r)) \in Reads;
    \* find the latest committed slot and pick a pending request
    with s = node[r].commitUpTo,
         v = IF s = 0 THEN "nil" ELSE node[r].insts[s].write,
         c = Head(UnseenPending(r))
    do
        \* acknowledge client directly with the latest committed value, and
        \* remove the command from pending
        Observe(<<ReqEvent(c), AckEvent(c, v)>>);
        Resolve(c);
    end with;
end macro;

\* A live replica may crash permanently.
macro ReplicaCrashes(r) begin
    await /\ NodeFailuresOn
          /\ ~crashed[r];
    \* mark myself as crashed
    crashed[r] := TRUE;
end macro;

\* Grantor f opens a new lease session toward its known leader. Gated by
\* the condition that f knows a leader and f is not actively granting to
\* anyone.
macro GrantorInitiateLease(f) begin
    await /\ node[f].leader # "none"
          /\ \A p \in Replicas: node[f].asGrantor[p].status = "None";
    with p = node[f].leader,
         newSeq = node[f].asGrantor[p].seq + 1 do
        node[f].asGrantor[p] :=
            [status |-> "Guarding",
             guardExpire |-> time[f] + TGuard,
             leaseExpire |-> 0,
             bal |-> node[f].balMaxKnown,
             seq |-> newSeq];
        Send({GuardMsg(f, p, node[f].balMaxKnown, newSeq)});
    end with;
end macro;

\* Grantee p receives a Guard from grantor f. Accept iff ballot is at least
\* as high as p's view and the message's seq is strictly higher than any seq
\* ever observed on this pair. If ballot rises, also revokes stale outgoing
\* lease grants from p.
macro HandleGuard(p) begin
    with m \in msgs do
        await /\ m.type = "Guard"
              /\ m.grantee = p
              /\ m.bal >= node[p].balMaxKnown
              /\ m.seq > node[p].asGrantee[m.grantor].seq
              /\ node[p].asGrantee[m.grantor].status = "None";
        \* update ballot in case higher, and start Guarded state; bump seq;
        \* also revoke any stale outgoing lease grants
        node[p].balMaxKnown := m.bal ||
        node[p].asGrantee[m.grantor] :=
            [status |-> "Guarded",
             guardExpire |-> time[p] + TGuard,
             leaseExpire |-> 0,
             bal |-> m.bal,
             seq |-> m.seq + 1] ||
        node[p].asGrantor := RevokeStaleAsGrantor(p, m.bal);
        \* reply GuardReply back to grantor, stamped with the new seq; also
        \* send Revokes for the just-Revoking outgoing grants
        Send(      {GuardReplyMsg(p, m.grantor, m.bal, m.seq + 1)}
              \cup RevokeStaleSendMsgs(p, m.bal));
    end with;
end macro;

\* Grantor f receives a GuardReply: transition asGrantor[m.grantee] from
\* Guarding to Renewing; send first Renew.
macro HandleGuardReply(f) begin
    with m \in msgs do
        await /\ m.type = "GuardReply"
              /\ m.grantor = f
              /\ m.bal = node[f].balMaxKnown
              /\ m.seq > node[f].asGrantor[m.grantee].seq
              /\ node[f].asGrantor[m.grantee].status = "Guarding";
        \* loose expiry for safety, tightened at first RenewReply
        node[f].asGrantor[m.grantee] :=
            [node[f].asGrantor[m.grantee] EXCEPT
                !.status = "Renewing",
                !.leaseExpire = time[f] + TGuard + TLease,
                !.seq = m.seq + 1];
        Send({RenewMsg(f, m.grantee, m.bal, m.seq + 1)});
    end with;
end macro;

\* Grantor f spontaneously sends a subsequent Renew to its current leader.
macro SpontaneousRenew(f) begin
    with p = node[f].leader do
        await /\ p # "none"
              /\ node[f].asGrantor[p].bal = node[f].balMaxKnown
              /\ node[f].asGrantor[p].status = "Renewing"
              /\ time[f] < node[f].asGrantor[p].leaseExpire
              /\ time[f] + TLease > node[f].asGrantor[p].leaseExpire;
        with newSeq = node[f].asGrantor[p].seq + 1,
             newExpire = node[f].asGrantor[p].leaseExpire + TLease do
            node[f].asGrantor[p] :=
                [node[f].asGrantor[p] EXCEPT
                    !.leaseExpire = newExpire,
                    !.seq = newSeq];
            Send({RenewMsg(f, p, node[f].balMaxKnown, newSeq)});
        end with;
    end with;
end macro;

\* Grantee p receives a Renew.
macro HandleRenew(p) begin
    with m \in msgs do
        await /\ m.type = "Renew"
              /\ m.grantee = p
              /\ m.bal = node[p].balMaxKnown
              /\ m.seq > node[p].asGrantee[m.grantor].seq
              /\ \/ /\ node[p].asGrantee[m.grantor].status = "Guarded"
                    /\ time[p] < node[p].asGrantee[m.grantor].guardExpire
                 \/ /\ node[p].asGrantee[m.grantor].status = "Renewed"
                    /\ time[p] < node[p].asGrantee[m.grantor].leaseExpire
                    /\ time[p] + TLease > node[p].asGrantee[m.grantor].leaseExpire;
        node[p].asGrantee[m.grantor] :=
            [node[p].asGrantee[m.grantor] EXCEPT
                !.status = "Renewed",
                !.leaseExpire = time[p] + TLease,
                !.bal = m.bal,
                !.seq = m.seq + 1];
        Send({RenewReplyMsg(p, m.grantor, m.bal, m.seq + 1)});
    end with;
end macro;

\* Grantor f receives a RenewReply; tightens down the loose expiry.
macro HandleRenewReply(f) begin
    with m \in msgs do
        await /\ m.type = "RenewReply"
              /\ m.grantor = f
              /\ m.bal = node[f].balMaxKnown
              /\ m.seq > node[f].asGrantor[m.grantee].seq
              /\ node[f].asGrantor[m.grantee].status = "Renewing"
              /\ time[f] + TLease > node[f].asGrantor[m.grantee].leaseExpire;
        node[f].asGrantor[m.grantee] :=
            [node[f].asGrantor[m.grantee] EXCEPT
                !.leaseExpire = time[f] + TLease,
                !.seq = m.seq];
    end with;
end macro;

\* Grantee p processes a Revoke from grantor f. If ballot rises, also
\* revokes stale outgoing lease grants from p.
macro HandleRevoke(p) begin
    with m \in msgs do
        await /\ m.type = "Revoke"
              /\ m.grantee = p
              /\ m.bal >= node[p].balMaxKnown
              /\ m.seq > node[p].asGrantee[m.grantor].seq
              /\ node[p].asGrantee[m.grantor].status \in {"Guarded", "Renewed"};
        \* update ballot in case higher, clear grantee state but preserve seq;
        \* also revoke any stale outgoing lease grants
        node[p].balMaxKnown := m.bal ||
        node[p].asGrantee[m.grantor] :=
            [NullGranteeState EXCEPT !.seq = m.seq + 1] ||
        node[p].asGrantor := RevokeStaleAsGrantor(p, m.bal);
        Send(      {RevokeReplyMsg(p, m.grantor, m.bal, m.seq + 1)}
              \cup RevokeStaleSendMsgs(p, m.bal));
    end with;
end macro;

\* Grantor f receives a RevokeReply; drops the lease promptly.
macro HandleRevokeReply(f) begin
    with m \in msgs do
        await /\ m.type = "RevokeReply"
              /\ m.grantor = f
              /\ m.bal = node[f].balMaxKnown
              /\ m.seq > node[f].asGrantor[m.grantee].seq
              /\ node[f].asGrantor[m.grantee].status = "Revoking";
        node[f].asGrantor[m.grantee] :=
            [NullGrantorState EXCEPT !.seq = m.seq];
    end with;
end macro;

\* Advances time by one tick globally, and garbage-collects expired lease
\* state. Per-pair seq counters are preserved across GC.
macro TimeTick() begin
    \* leasing requires nodes to align on how fast time flies (bounded clock
    \* drift); for simplicity, this spec advances all nodes' clocks by the same
    \* mount of 1; in practice, bounded epsilon differences are tolerated
    time := [r \in Replicas |-> time[r] + 1];
    node := [r \in Replicas |->
        [node[r] EXCEPT
            !.asGrantor =
                [p \in Replicas |->
                    IF \/ /\ node[r].asGrantor[p].status \in {"Renewing", "Revoking"}
                          /\ node[r].asGrantor[p].leaseExpire =< time[r]
                       \/ /\ node[r].asGrantor[p].status = "Guarding"
                          /\ node[r].asGrantor[p].guardExpire =< time[r]
                      THEN [NullGrantorState EXCEPT !.seq = node[r].asGrantor[p].seq]
                      ELSE node[r].asGrantor[p]],
            !.asGrantee =
                [f \in Replicas |->
                    IF \/ /\ node[r].asGrantee[f].status = "Renewed"
                          /\ node[r].asGrantee[f].leaseExpire =< time[r]
                       \/ /\ node[r].asGrantee[f].status = "Guarded"
                          /\ node[r].asGrantee[f].guardExpire =< time[r]
                      THEN [NullGranteeState EXCEPT !.seq = node[r].asGrantee[f].seq]
                      ELSE node[r].asGrantee[f]]]];
end macro;

\* Replica server node main loop.
process Replica \in Replicas
begin
    rloop: while (~terminated) /\ (~crashed[self]) do
        either
            BecomeLeader(self);
        or
            HandlePrepare(self);
        or
            HandlePrepareReplies(self);
        or
            TakeNewWriteRequest(self);
        or
            HandleAccept(self);
        or
            HandleAcceptReplies(self);
        or
            HandleCommitNotice(self);
        or
            TakeNewReadRequest(self);
        or
            GrantorInitiateLease(self);
        or
            HandleGuard(self);
        or
            HandleGuardReply(self);
        or
            SpontaneousRenew(self);
        or
            HandleRenew(self);
        or
            HandleRenewReply(self);
        or
            HandleRevoke(self);
        or
            HandleRevokeReply(self);
        or
            TimeTick();
        or
            ReplicaCrashes(self);
        end either;
    end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "1fbd19f8" /\ chksum(tla) = "9a7c41f2")
VARIABLES pc, msgs, node, pending, observed, crashed, time

(* define statement *)
FGrantsPWithBal(f, p, b) == /\ node[p].asGrantee[f].status = "Renewed"
                            /\ node[p].asGrantee[f].leaseExpire > time[p]
                            /\ node[p].asGrantee[f].bal = b


ThinkAmLeader(r) ==
    /\ node[r].leader = r
    /\ node[r].balPrepared = node[r].balMaxKnown
    /\ Cardinality({f \in Replicas:
                    FGrantsPWithBal(f, r, node[r].balMaxKnown)})
       >= MajorityNum





RevokeStaleAsGrantor(r, nb) ==
    [p \in Replicas |->
        LET g == node[r].asGrantor[p]
        IN  IF      /\ g.bal < nb
                    /\ g.status = "Guarding"
                    /\ g.guardExpire > time[r]
                THEN [NullGrantorState EXCEPT !.seq = g.seq]
            ELSE IF /\ g.bal < nb
                    /\ g.status = "Renewing"
                    /\ g.leaseExpire > time[r]
                THEN [g EXCEPT !.status = "Revoking", !.seq = g.seq + 1]
            ELSE g]



RevokeStaleSendMsgs(r, nb) ==
    {RevokeMsg(r, p, nb, node[r].asGrantor[p].seq + 1):
     p \in {p \in Replicas: /\ node[r].asGrantor[p].bal < nb
                            /\ node[r].asGrantor[p].status = "Renewing"
                            /\ node[r].asGrantor[p].leaseExpire > time[r]}}


AppendObserved(seq) ==
    LET filter(e) == e \notin Range(observed)
    IN  observed \o SelectSeq(seq, filter)

UnseenPending(r) ==
    LET filter(c) == \A s \in Slots: node[r].insts[s].write # c
    IN  SelectSeq(pending, filter)

RemovePending(cmd) ==
    LET filter(c) == c # cmd
    IN  SelectSeq(pending, filter)

reqsMade == {e.cmd: e \in {e \in Range(observed): e.type = "Req"}}

acksRecv == {e.cmd: e \in {e \in Range(observed): e.type = "Ack"}}

terminated == /\ Len(pending) = 0
              /\ Cardinality(reqsMade) = NumCommands
              /\ Cardinality(acksRecv) = NumCommands

NodeFailuresOn == TRUE


vars == << pc, msgs, node, pending, observed, crashed, time >>

ProcSet == (Replicas)

Init == (* Global variables *)
        /\ msgs = {}
        /\ node = [r \in Replicas |-> NullNode]
        /\ pending = InitPending
        /\ observed = <<>>
        /\ crashed = [r \in Replicas |-> FALSE]
        /\ time = [r \in Replicas |-> 1]
        /\ pc = [self \in ProcSet |-> "rloop"]

rloop(self) == /\ pc[self] = "rloop"
               /\ IF (~terminated) /\ (~crashed[self])
                     THEN /\ \/ /\ node[self].leader # self
                                /\ \E b \in Ballots:
                                     /\ /\ b > node[self].balMaxKnown
                                        /\ ~\E m \in msgs: (m.type = "Prepare") /\ (m.bal = b)
                                     /\ node' = [node EXCEPT ![self].leader = self,
                                                             ![self].balPrepared = 0,
                                                             ![self].balMaxKnown = b,
                                                             ![self].insts = [s \in Slots |->
                                                                                 [node[self].insts[s]
                                                                                     EXCEPT !.status = IF @ = "Accepting"
                                                                                                         THEN "Preparing"
                                                                                                         ELSE @]],
                                                             ![self].asGrantor = RevokeStaleAsGrantor(self, b)]
                                     /\ msgs' = (msgs \cup (     {PrepareMsg(self, b),
                                                                  PrepareReplyMsg(self, b, VotesByNode(node'[self]))}
                                                 \cup RevokeStaleSendMsgs(self, b)))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "Prepare"
                                        /\ m.bal > node[self].balMaxKnown
                                     /\ node' = [node EXCEPT ![self].leader = m.src,
                                                             ![self].balMaxKnown = m.bal,
                                                             ![self].insts = [s \in Slots |->
                                                                                 [node[self].insts[s]
                                                                                     EXCEPT !.status = IF @ = "Accepting"
                                                                                                         THEN "Preparing"
                                                                                                         ELSE @]],
                                                             ![self].asGrantor = RevokeStaleAsGrantor(self, m.bal)]
                                     /\ msgs' = (msgs \cup (     {PrepareReplyMsg(self, m.bal, VotesByNode(node'[self]))}
                                                 \cup RevokeStaleSendMsgs(self, m.bal)))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ /\ node[self].leader = self
                                   /\ node[self].balPrepared = 0
                                /\ LET prs == {m \in msgs: /\ m.type = "PrepareReply"
                                                           /\ m.bal = node[self].balMaxKnown} IN
                                     /\ Cardinality(prs) >= MajorityNum
                                     /\ \E prsGot \in {prsGot \in SUBSET prs:
                                                       Cardinality(prsGot) >= MajorityNum}:
                                          LET lts == LastTouchedSlot(prsGot) IN
                                            /\ node' = [node EXCEPT ![self].balPrepared = node[self].balMaxKnown,
                                                                    ![self].insts = [s \in Slots |->
                                                                                        LET pvw == PeakVotedWrite(prsGot, s)
                                                                                            adopted == \/ node[self].insts[s].status = "Preparing"
                                                                                                       \/ /\ node[self].insts[s].status = "Empty"
                                                                                                          /\ pvw # "nil"
                                                                                        IN  [node[self].insts[s]
                                                                                                EXCEPT !.status = IF adopted
                                                                                                                    THEN "Accepting"
                                                                                                                    ELSE @,
                                                                                                       !.write  = pvw,
                                                                                                       !.voted  = IF adopted
                                                                                                                    THEN [bal |-> node[self].balMaxKnown,
                                                                                                                          write |-> pvw]
                                                                                                                    ELSE @]],
                                                                    ![self].commitPrev = lts]
                                            /\ msgs' = (msgs \cup (UNION
                                                                   {{AcceptMsg(self, node'[self].balPrepared, s, node'[self].insts[s].write),
                                                                     AcceptReplyMsg(self, node'[self].balPrepared, s)}:
                                                                    s \in {s \in Slots: node'[self].insts[s].status = "Accepting"}}))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ /\ ThinkAmLeader(self)
                                   /\ \E s \in Slots: node[self].insts[s].status = "Empty"
                                   /\ Len(UnseenPending(self)) > 0
                                   /\ Head(UnseenPending(self)) \in Writes
                                /\ LET s == FirstEmptySlot(node[self].insts) IN
                                     LET c == Head(UnseenPending(self)) IN
                                       /\ node' = [node EXCEPT ![self].insts[s].status = "Accepting",
                                                               ![self].insts[s].write = c,
                                                               ![self].insts[s].voted.bal = node[self].balPrepared,
                                                               ![self].insts[s].voted.write = c]
                                       /\ msgs' = (msgs \cup ({AcceptMsg(self, node'[self].balPrepared, s, c),
                                                               AcceptReplyMsg(self, node'[self].balPrepared, s)}))
                                       /\ observed' = AppendObserved((<<ReqEvent(c)>>))
                                /\ UNCHANGED <<pending, crashed, time>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "Accept"
                                        /\ m.bal >= node[self].balMaxKnown
                                        /\ m.bal >= node[self].insts[m.slot].voted.bal
                                     /\ node' = [node EXCEPT ![self].leader = m.src,
                                                             ![self].balMaxKnown = m.bal,
                                                             ![self].insts[m.slot].status = "Accepting",
                                                             ![self].insts[m.slot].write = m.write,
                                                             ![self].insts[m.slot].voted.bal = m.bal,
                                                             ![self].insts[m.slot].voted.write = m.write,
                                                             ![self].asGrantor = RevokeStaleAsGrantor(self, m.bal)]
                                     /\ msgs' = (msgs \cup (     {AcceptReplyMsg(self, m.bal, m.slot)}
                                                 \cup RevokeStaleSendMsgs(self, m.bal)))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ /\ ThinkAmLeader(self)
                                   /\ node[self].commitUpTo < NumWrites
                                   /\ node[self].insts[node[self].commitUpTo + 1].status = "Accepting"
                                /\ LET s == node[self].commitUpTo + 1 IN
                                     LET c == node[self].insts[s].write IN
                                       LET ps == s - 1 IN
                                         LET v == IF ps = 0 THEN "nil" ELSE node[self].insts[ps].write IN
                                           LET ars == {m \in msgs: /\ m.type = "AcceptReply"
                                                                   /\ m.slot = s
                                                                   /\ m.bal = node[self].balPrepared} IN
                                             /\ Cardinality(ars) >= MajorityNum
                                             /\ \E arsGot \in {arsGot \in SUBSET ars:
                                                               Cardinality(arsGot) >= MajorityNum}:
                                                  /\ node' = [node EXCEPT ![self].insts[s].status = "Committed",
                                                                          ![self].commitUpTo = s]
                                                  /\ observed' = AppendObserved((<<AckEvent(c, v)>>))
                                                  /\ pending' = RemovePending(c)
                                                  /\ msgs' = (msgs \cup ({CommitNoticeMsg(s)}))
                                /\ UNCHANGED <<crashed, time>>
                             \/ /\ /\ node[self].leader # self
                                   /\ node[self].commitUpTo < NumWrites
                                   /\ node[self].insts[node[self].commitUpTo + 1].status = "Accepting"
                                /\ LET s == node[self].commitUpTo + 1 IN
                                     LET c == node[self].insts[s].write IN
                                       \E m \in msgs:
                                         /\ /\ m.type = "CommitNotice"
                                            /\ m.upto = s
                                         /\ node' = [node EXCEPT ![self].insts[s].status = "Committed",
                                                                 ![self].commitUpTo = s]
                                /\ UNCHANGED <<msgs, pending, observed, crashed, time>>
                             \/ /\ /\ ThinkAmLeader(self)
                                   /\ node[self].commitUpTo >= node[self].commitPrev
                                   /\ Len(UnseenPending(self)) > 0
                                   /\ Head(UnseenPending(self)) \in Reads
                                /\ LET s == node[self].commitUpTo IN
                                     LET v == IF s = 0 THEN "nil" ELSE node[self].insts[s].write IN
                                       LET c == Head(UnseenPending(self)) IN
                                         /\ observed' = AppendObserved((<<ReqEvent(c), AckEvent(c, v)>>))
                                         /\ pending' = RemovePending(c)
                                /\ UNCHANGED <<msgs, node, crashed, time>>
                             \/ /\ /\ node[self].leader # "none"
                                   /\ \A p \in Replicas: node[self].asGrantor[p].status = "None"
                                /\ LET p == node[self].leader IN
                                     LET newSeq == node[self].asGrantor[p].seq + 1 IN
                                       /\ node' = [node EXCEPT ![self].asGrantor[p] = [status |-> "Guarding",
                                                                                       guardExpire |-> time[self] + TGuard,
                                                                                       leaseExpire |-> 0,
                                                                                       bal |-> node[self].balMaxKnown,
                                                                                       seq |-> newSeq]]
                                       /\ msgs' = (msgs \cup ({GuardMsg(self, p, node'[self].balMaxKnown, newSeq)}))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "Guard"
                                        /\ m.grantee = self
                                        /\ m.bal >= node[self].balMaxKnown
                                        /\ m.seq > node[self].asGrantee[m.grantor].seq
                                        /\ node[self].asGrantee[m.grantor].status = "None"
                                     /\ node' = [node EXCEPT ![self].balMaxKnown = m.bal,
                                                             ![self].asGrantee[m.grantor] = [status |-> "Guarded",
                                                                                             guardExpire |-> time[self] + TGuard,
                                                                                             leaseExpire |-> 0,
                                                                                             bal |-> m.bal,
                                                                                             seq |-> m.seq + 1],
                                                             ![self].asGrantor = RevokeStaleAsGrantor(self, m.bal)]
                                     /\ msgs' = (msgs \cup (     {GuardReplyMsg(self, m.grantor, m.bal, m.seq + 1)}
                                                 \cup RevokeStaleSendMsgs(self, m.bal)))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "GuardReply"
                                        /\ m.grantor = self
                                        /\ m.bal = node[self].balMaxKnown
                                        /\ m.seq > node[self].asGrantor[m.grantee].seq
                                        /\ node[self].asGrantor[m.grantee].status = "Guarding"
                                     /\ node' = [node EXCEPT ![self].asGrantor[m.grantee] = [node[self].asGrantor[m.grantee] EXCEPT
                                                                                                !.status = "Renewing",
                                                                                                !.leaseExpire = time[self] + TGuard + TLease,
                                                                                                !.seq = m.seq + 1]]
                                     /\ msgs' = (msgs \cup ({RenewMsg(self, m.grantee, m.bal, m.seq + 1)}))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ LET p == node[self].leader IN
                                     /\ /\ p # "none"
                                        /\ node[self].asGrantor[p].bal = node[self].balMaxKnown
                                        /\ node[self].asGrantor[p].status = "Renewing"
                                        /\ time[self] < node[self].asGrantor[p].leaseExpire
                                        /\ time[self] + TLease > node[self].asGrantor[p].leaseExpire
                                     /\ LET newSeq == node[self].asGrantor[p].seq + 1 IN
                                          LET newExpire == node[self].asGrantor[p].leaseExpire + TLease IN
                                            /\ node' = [node EXCEPT ![self].asGrantor[p] = [node[self].asGrantor[p] EXCEPT
                                                                                               !.leaseExpire = newExpire,
                                                                                               !.seq = newSeq]]
                                            /\ msgs' = (msgs \cup ({RenewMsg(self, p, node'[self].balMaxKnown, newSeq)}))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "Renew"
                                        /\ m.grantee = self
                                        /\ m.bal = node[self].balMaxKnown
                                        /\ m.seq > node[self].asGrantee[m.grantor].seq
                                        /\ \/ /\ node[self].asGrantee[m.grantor].status = "Guarded"
                                              /\ time[self] < node[self].asGrantee[m.grantor].guardExpire
                                           \/ /\ node[self].asGrantee[m.grantor].status = "Renewed"
                                              /\ time[self] < node[self].asGrantee[m.grantor].leaseExpire
                                              /\ time[self] + TLease > node[self].asGrantee[m.grantor].leaseExpire
                                     /\ node' = [node EXCEPT ![self].asGrantee[m.grantor] = [node[self].asGrantee[m.grantor] EXCEPT
                                                                                                !.status = "Renewed",
                                                                                                !.leaseExpire = time[self] + TLease,
                                                                                                !.bal = m.bal,
                                                                                                !.seq = m.seq + 1]]
                                     /\ msgs' = (msgs \cup ({RenewReplyMsg(self, m.grantor, m.bal, m.seq + 1)}))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "RenewReply"
                                        /\ m.grantor = self
                                        /\ m.bal = node[self].balMaxKnown
                                        /\ m.seq > node[self].asGrantor[m.grantee].seq
                                        /\ node[self].asGrantor[m.grantee].status = "Renewing"
                                        /\ time[self] + TLease > node[self].asGrantor[m.grantee].leaseExpire
                                     /\ node' = [node EXCEPT ![self].asGrantor[m.grantee] = [node[self].asGrantor[m.grantee] EXCEPT
                                                                                                !.leaseExpire = time[self] + TLease,
                                                                                                !.seq = m.seq]]
                                /\ UNCHANGED <<msgs, pending, observed, crashed, time>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "Revoke"
                                        /\ m.grantee = self
                                        /\ m.bal >= node[self].balMaxKnown
                                        /\ m.seq > node[self].asGrantee[m.grantor].seq
                                        /\ node[self].asGrantee[m.grantor].status \in {"Guarded", "Renewed"}
                                     /\ node' = [node EXCEPT ![self].balMaxKnown = m.bal,
                                                             ![self].asGrantee[m.grantor] = [NullGranteeState EXCEPT !.seq = m.seq + 1],
                                                             ![self].asGrantor = RevokeStaleAsGrantor(self, m.bal)]
                                     /\ msgs' = (msgs \cup (     {RevokeReplyMsg(self, m.grantor, m.bal, m.seq + 1)}
                                                 \cup RevokeStaleSendMsgs(self, m.bal)))
                                /\ UNCHANGED <<pending, observed, crashed, time>>
                             \/ /\ \E m \in msgs:
                                     /\ /\ m.type = "RevokeReply"
                                        /\ m.grantor = self
                                        /\ m.bal = node[self].balMaxKnown
                                        /\ m.seq > node[self].asGrantor[m.grantee].seq
                                        /\ node[self].asGrantor[m.grantee].status = "Revoking"
                                     /\ node' = [node EXCEPT ![self].asGrantor[m.grantee] = [NullGrantorState EXCEPT !.seq = m.seq]]
                                /\ UNCHANGED <<msgs, pending, observed, crashed, time>>
                             \/ /\ time' = [r \in Replicas |-> time[r] + 1]
                                /\ node' =     [r \in Replicas |->
                                           [node[r] EXCEPT
                                               !.asGrantor =
                                                   [p \in Replicas |->
                                                       IF \/ /\ node[r].asGrantor[p].status \in {"Renewing", "Revoking"}
                                                             /\ node[r].asGrantor[p].leaseExpire =< time'[r]
                                                          \/ /\ node[r].asGrantor[p].status = "Guarding"
                                                             /\ node[r].asGrantor[p].guardExpire =< time'[r]
                                                         THEN [NullGrantorState EXCEPT !.seq = node[r].asGrantor[p].seq]
                                                         ELSE node[r].asGrantor[p]],
                                               !.asGrantee =
                                                   [f \in Replicas |->
                                                       IF \/ /\ node[r].asGrantee[f].status = "Renewed"
                                                             /\ node[r].asGrantee[f].leaseExpire =< time'[r]
                                                          \/ /\ node[r].asGrantee[f].status = "Guarded"
                                                             /\ node[r].asGrantee[f].guardExpire =< time'[r]
                                                         THEN [NullGranteeState EXCEPT !.seq = node[r].asGrantee[f].seq]
                                                         ELSE node[r].asGrantee[f]]]]
                                /\ UNCHANGED <<msgs, pending, observed, crashed>>
                             \/ /\ /\ NodeFailuresOn
                                   /\ ~crashed[self]
                                /\ crashed' = [crashed EXCEPT ![self] = TRUE]
                                /\ UNCHANGED <<msgs, node, pending, observed, time>>
                          /\ pc' = [pc EXCEPT ![self] = "rloop"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << msgs, node, pending, observed, 
                                          crashed, time >>

Replica(self) == rloop(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Replicas: Replica(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

----------

(*************************)
(* Type check invariant. *)
(*************************)
TypeOK == /\ msgs \in SUBSET Messages
          /\ node \in [Replicas -> NodeStates]
          /\ time \in [Replicas -> Times]
          /\ pending \in Seq(Commands)
          /\ observed \in Seq(ClientEvents)
          /\ crashed \in [Replicas -> BOOLEAN]
          /\ pc \in [Replicas -> {"rloop", "Done"}]
          \* Additional bounds and consistency checks for client state.
          /\ Len(pending) =< NumCommands
          /\ IsInjective(pending)
          /\ Len(observed) =< 2 * NumCommands
          /\ IsInjective(observed)
          /\ Cardinality(reqsMade) >= Cardinality(acksRecv)

THEOREM Spec => []TypeOK

----------

(*************************************)
(* Lease expiration safety property. *)
(*************************************)
LeaseExpirationSafety ==
    \A f, p \in Replicas:
        (/\ node[p].asGrantee[f].status = "Renewed"
         /\ node[p].asGrantee[f].leaseExpire > time[p])
            => (/\ node[f].asGrantor[p].status \in {"Renewing", "Revoking"}
                /\ node[f].asGrantor[p].leaseExpire
                   >= node[p].asGrantee[f].leaseExpire)

THEOREM Spec => []LeaseExpirationSafety

----------

(******************************************)
(* Lease uniqueness guarantee assertions. *)
(******************************************)
AtMostGrantsOneLeader ==
    \A f \in Replicas, b \in Ballots:
        Cardinality({p \in Replicas: FGrantsPWithBal(f, p, b)}) =< 1

HasLeaseQuorum(p) ==
    Cardinality({f \in Replicas:
                 FGrantsPWithBal(f, p, node[p].balMaxKnown)}) >= MajorityNum

AtMostOneStableLeader ==
    \A p1, p2 \in Replicas:
        (HasLeaseQuorum(p1) /\ HasLeaseQuorum(p2)) => (p1 = p2)

THEOREM Spec => /\ []AtMostGrantsOneLeader
                /\ []AtMostOneStableLeader

====
