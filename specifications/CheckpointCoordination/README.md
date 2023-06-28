# Ringmaster Checkpoint Coordination

This spec was written in June 2017 while the author worked in Microsoft Azure Networking, on the Azure DNS team.
At the time the Azure DNS backend used an in-memory tree database called [RingMaster](https://github.com/Azure/RingMaster) built on top of a Paxos implementation called the [Replicated State Library (RSL)](https://github.com/Azure/RSL).
Both of those systems were long ago released as open source, and now this spec has followed.
This spec was written while designing a checkpoint/backup coordination feature described below.
It is notable for two reasons:
 1. The TLC model checker found a 12-step error trace for a very subtle bug introduced by an attempted optimization
 2. The actual feature was implemented directly after the spec was written, providing an account of the experience of writing a program following a TLA⁺ spec

Both of these points are covered in detail in [this](https://ahelwer.ca/post/2023-04-05-checkpoint-coordination) blog post.
What follows is the informal-language feature spec distributed alongside the TLA⁺ spec.

## The Problem

### Summary & Motivation

There are five replicas in a Ring Master cluster, one of which is elected primary at any given time.
The other four replicas are secondaries.
These secondaries must occasionally take a checkpoint of their local state and upload the resulting codex to cloud storage as a backup.
Currently, the secondaries take checkpoints at random.
This means that occasionally multiple secondary replicas take checkpoints simultaneously.
We want to begin performing read operations on secondaries, which is not possible while they are taking a checkpoint.
Thus, we want only one secondary replica to take a checkpoint at any given time.
We furthermore wish for the replicas to rotate evenly through taking a checkpoint.
This is a distributed coordination problem.

### Invariants

The system has the following invariants, which must hold true in every state:

 * Safety invariant: the primary never takes a checkpoint
 * Safety invariant: multiple secondary replicas never take a checkpoint concurrently
 * Temporal invariant: all secondary replicas eventually take a checkpoint
 * Temporal invariant: a checkpoint always eventually completes or is aborted

### Failure Model

We want our system to gracefully handle the following failure modes:

 * Replicas crashing, then later recovering
 * Network links failing between any two replicas in the cluster, then recovering
 * The rate of passage of time differing between replicas

### Discarded Approaches

We considered a simple time slice approach, where each replica is allocated a slice of time in an uncoordinated round-robin fashion.
For example, each replica calculates the number of hours passed since some shared fixed date in the past modulo the number of replicas in the cluster; the result maps uniquely onto a replica in the cluster, which has that hour to take a checkpoint.
This approach was discarded with the following objections:

 * Requires coordination mechanism to adaptively vary time slice size, removing advantage
 * Local time passage rate can vary between replicas, causing them to drift out of coordination
 * Inefficient: primary does not take backup, so hour is wasted; similar if replica is down
 
We considered an approach like the above based on RSL decree numbers instead of real time, but this was considered unreliable as the rate of new decrees can vary widely; this gives inconsistent slices of real time to take a checkpoint.

## Solution

### Outline

We developed a randomized turn-based solution: the primary selects a secondary replica to take a checkpoint, weighted so healthier replicas are selected more often.
The primary then uses the RSL consensus mechanism (via the `ManagedRSLStateMachine.ReplicateRequest` method) to issue a checkpoint lease to the selected secondary.

Secondary replicas receive & process the checkpoint lease message via their implementation of the abstract `ManagedRSLStateMachine.ExecuteReplicatedRequest` method.
If the checkpoint lease applies to the secondary replica processing the message, it schedules a checkpoint.

### Sub-Problem: Checkpoint Lease Revocation

A problem arises with checkpoint timeouts & aborts: once a secondary replica begins taking a checkpoint, it stops processing further replicated requests (although it continues to participate in the RSL Paxos rounds); the requests are stored in a log to be executed after checkpoint completion.
Thus, we lack a mechanism for the primary to directly revoke a secondary's checkpoint lease.

The “best” solution to the checkpoint lease revocation problem is a modification to the RSL library itself exposing a separate checkpoint coordination-specific API which executes regardless of whether the secondary is taking a checkpoint, but in the interest of simplicity and expediency we are instead using coordinated timeouts between primary and secondary.
This means the primary will decide on a local timeout after which it will issue a new checkpoint lease; the same timeout is also given to the secondary, which is assumed to be running in a similar reference frame.
When the timeout expires on the secondary, it is expected to abort its checkpoint if not yet complete.

The timeout coordination solution to the checkpoint lease revocation problem runs afoul of our failure model: we cannot assume time passes at the same rate on each replica.
However, RSL's heartbeat system ensures a difference of at most 30% (configurable) in time passed between primary and secondary – so one second on the primary synchronizes with at least 0.7 seconds on the secondary.
Thus, if the secondary sets its checkpoint timeout as 70% of the timeout given by the primary, it is guaranteed to either finish its checkpoint before the timeout, timeout before the primary, or be kicked out of the replica set.

### Sub-Problem: Adaptive Checkpoint Timeouts
 
To avoid manual intervention, the timeout decided by the primary must adapt to reality.
If a replica times out before completing a checkpoint, the primary should allocate a larger length of time.
Inversely, if a replica completes a checkpoint before timeout this may mean the timeout is too long and should be adjusted downward.
The adaptive timeout calculation has one requirement: secondaries communicate their checkpoint completion (or lack thereof) back to the primary.
Replica health reports contain a 64-bit field (`ManagedReplicaHealth.LastVotePayload`) for piggybacking status updates to the primary.
Upon completion of a checkpoint, a secondary will persistently fill this payload with the RSL sequence number up to which the checkpoint applied (it is zero by default).
The primary will either see this value and register completion of the checkpoint, or fail to see the value within its local timeout period and register a timeout.

A global absolute maximum timeout is pre-defined to cap runaway checkpoint time budgets.

### Sub-Problem: Lease Handover on Primary Failover

The case of primary failover during an active checkpoint lease requires special scrutiny.
First, note that the new primary will have seen and executed the replicated request containing the currently-active checkpoint lease, as a secondary.
We know this because we require replicas to be fully caught up before being elected primary.
The new primary maintained this lease data in-memory, and upon primary election appears situated to properly calculate the timeout of the current lease.
There is, however, a possible problem – what if the new primary is in a reference frame where time runs faster than the reference frame of the old secondary?
For example:

|     Role    | Time Dilation | Lease Start Time | Elapsed Local Time | Local Time  |  
| ----------- | ------------- | ---------------- | ------------------ | ----------- |  
| Old Primary | 1.0x          | T = 0            | 10s                | T = 10s     |  
| Secondary   | 1.25x         | T' = 0           | 8s                 | T' = 8s     |  
| New Primary | 0.8x          | T'' = 0          | 12.5s              | T'' = 12.5s |  

If the checkpoint lease was issued by the old primary to the secondary at T = 0 with a local timeout of 10 seconds, then the secondary uses a local timeout of 0.7\*10 = 7 seconds.
Consider a primary failover at T = 8s, so T' = 6.4s and T'' = 10s.
We might be concerned that the new primary believes the lease has timed out, so issues a new lease to a different replica – thus violating our safety invariant of never having multiple replicas taking a checkpoint concurrently.
However, if we can rely on the RSL heartbeat system to instantly boot the secondary from the replica set (since its time dilation relative to the primary is 1.6, below the 70% threshold) once the new primary comes online, this problem is taken care of.

### Sub-Problem: Primary Lacks Knowledge of Lease

Will there ever be a case where a replica becomes primary with no knowledge of an active checkpoint lease, despite such a lease existing?
Let us consider cases where a replica becomes leader without knowledge of an active checkpoint lease, regardless of whether such a lease exists:

 * The cluster was just created and no checkpoint lease has yet been issued in its history 
 * A somewhat complicated execution trace: 
    1. Checkpoint lease given to secondary A 
    2. Secondary A finishes checkpoint before timeout 
    3. Secondary B dies 
    4. Secondary B recovers 
    5. Secondary B is rehydrated from checkpoint created by secondary A 
    6. Leader dies 
    7. Secondary B becomes leader

In both cases, even though no knowledge of an existing lease is present, it is safe for the primary to issue a new lease immediately.
In the second case, we are saved by the requirement that all replicas elected leader must have executed (not merely possessed) all chosen transactions before acting as leader.
If our requirement were weaker – a replica can be elected by possessing all transactions but not executing them – then we could possibly issue a new checkpoint lease while an existing checkpoint lease sits in our log of unprocessed transactions.

### Pitfall: Attempted Optimization of Lease Pre-emption

The original system design optimized the case of a node being elected leader while in possession of the most-current checkpoint lease.
Since the leader cannot take a checkpoint, the node would immediately issue a new checkpoint lease to one of the secondaries.
However, this resulted in the following twelve-step error trace for a three-node system:
1. Initial state with nodes `n1`, `n2`, and `n3`
2. `n1` elected leader
3. `n1` sends replicated request `1` assigning checkpoint lease to `n2`
4. `n1` dies
5. `n2` executes replicated request `1` and marks self as able to take checkpoint
6. `n2` elected leader
7. `n2` sees self in possession of checkpoint lease, so (using optimization rule) pre-empts it and issues replicated request `2` assigning checkpoint lease to `n3`
8. `n2` dies
9. `n2` recovers
10. `n2` executes replicated request `1` again, marks self able to take checkpoint
11. `n3` executes replicated request `1`, knows `n2` can take checkpoint
12. `n3` executes replicated request `2`, marks self able to take checkpoint

So between steps 10 and 12, both `n2` and `n3` end up believing they can take a checkpoint: a violation of our invariant that it is never the case that multiple nodes believe they can take a checkpoint simultaneously.
This is all due to the use of the lease pre-emption optimization in step 7.
Removing this attempted optimization rule solves the problem; instead of issuing a new lease immediately, the leader node simply waits for the lease (extended to itself) to time out before issuing another.

The `MCCheckpointCoordinationFailure.cfg` model reproduces the above error trace.

