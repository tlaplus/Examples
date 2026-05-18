# Deli

A TLA⁺ specification of a deli ordering system with ticket-based queuing and parallel service.

Customers arrive at any time, take a ticket number, and join a FIFO queue. Multiple workers independently pick up the next waiting customer, prepare their order, serve them, and return to idle. Because each worker tracks its own state, several customers can be served concurrently when multiple workers are available.

## Design

- **No global state**: Instead of a single shop-wide phase variable, each worker has its own state (`Idle`, `Preparing`, `Serving`), enabling true parallelism
- **Ticket-based customers**: Customers are identified by ticket numbers (1, 2, 3, …) rather than named processes, keeping the model simple and the `Arrive` action always enabled
- **FIFO queue discipline**: Customers are served in arrival order; the `QueueOrdered` invariant verifies this
- **State constraint for bounding**: The `arrivals` counter has no guard in the spec itself; a `CONSTRAINT arrivals <= 3` in the config file bounds exploration for model checking without polluting the specification
- **No `CHECK_DEADLOCK FALSE`**: Because `Arrive` is always enabled (ungated), every reachable state has at least one successor, so deadlock checking works naturally

## Properties Verified

The specification includes five safety invariants, all verified by TLC:

1. **TypeOK**: All state variables maintain their declared types
2. **IdleConsistency**: A worker is idle if and only if it has no customer assignment
3. **NoDoubleAssignment**: No two workers are ever assigned the same customer
4. **TicketStatePartition**: Every issued ticket is in exactly one logical state—queued, assigned to a worker, or served—with no overlaps and no lost tickets
5. **QueueOrdered**: Ticket numbers in the queue are strictly increasing (FIFO preserved)

The spec also defines `FairSpec` with weak fairness on each worker's actions, suitable for verifying liveness properties (e.g., every arriving customer is eventually served).
