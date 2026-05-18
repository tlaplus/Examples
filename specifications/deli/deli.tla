-------------------------------- MODULE deli --------------------------------
(***************************************************************************)
(* A specification of a deli ordering system with ticket-based queuing     *)
(* and parallel service by multiple workers.                               *)
(*                                                                         *)
(* Customers arrive at any time, take the next ticket number, and join a   *)
(* FIFO queue. Idle workers independently pick up the next waiting         *)
(* customer, prepare their order, serve them, and return to idle.          *)
(* Multiple workers operate concurrently, allowing several customers to    *)
(* be served in parallel.                                                  *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Workers, MaxArrivals

VARIABLES
    arrivals,        \* Nat: count of customers who have arrived
    queue,           \* Seq(Nat): FIFO queue of ticket numbers waiting
    workerState,     \* [Workers -> {"Idle", "Preparing", "Serving"}]
    workerCustomer,  \* [Workers -> Nat]: ticket number each worker handles (0 = none)
    served           \* Set of ticket numbers already served

vars == <<arrivals, queue, workerState, workerCustomer, served>>

(***************************************************************************)
(* Helper: the set of elements in a sequence.                              *)
(***************************************************************************)
Range(s) == { s[i] : i \in DOMAIN s }

---------------------------------------------------------------------------

(***************)
(* Type check  *)
(***************)

TypeOK ==
    /\ arrivals \in Nat
    /\ queue \in Seq(1..arrivals)
    /\ workerState \in [Workers -> {"Idle", "Preparing", "Serving"}]
    /\ workerCustomer \in [Workers -> Nat]
    /\ served \subseteq 1..arrivals

---------------------------------------------------------------------------

(*****************)
(* Initial state *)
(*****************)

Init ==
    /\ arrivals = 0
    /\ queue = <<>>
    /\ workerState = [w \in Workers |-> "Idle"]
    /\ workerCustomer = [w \in Workers |-> 0]
    /\ served = {}

---------------------------------------------------------------------------

(***********)
(* Actions *)
(***********)

(* A new customer arrives, takes the next ticket, and joins the queue. *)
(* This action has no guard and is always enabled; the arrivals count  *)
(* is bounded only by the state constraint in the model config.        *)
Arrive ==
    /\ arrivals' = arrivals + 1
    /\ queue' = Append(queue, arrivals + 1)
    /\ UNCHANGED <<workerState, workerCustomer, served>>

(* An idle worker picks up the next customer from the head of the queue *)
AssignWorker(w) ==
    /\ workerState[w] = "Idle"
    /\ queue /= <<>>
    /\ workerCustomer' = [workerCustomer EXCEPT ![w] = Head(queue)]
    /\ workerState' = [workerState EXCEPT ![w] = "Preparing"]
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<arrivals, served>>

(* A worker finishes preparing and begins serving *)
FinishPreparing(w) ==
    /\ workerState[w] = "Preparing"
    /\ workerState' = [workerState EXCEPT ![w] = "Serving"]
    /\ UNCHANGED <<arrivals, queue, workerCustomer, served>>

(* A worker completes service: customer is marked served, worker goes idle *)
CompleteService(w) ==
    /\ workerState[w] = "Serving"
    /\ served' = served \cup {workerCustomer[w]}
    /\ workerState' = [workerState EXCEPT ![w] = "Idle"]
    /\ workerCustomer' = [workerCustomer EXCEPT ![w] = 0]
    /\ UNCHANGED <<arrivals, queue>>

---------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)

Next ==
    \/ Arrive
    \/ \E w \in Workers : AssignWorker(w) \/ FinishPreparing(w) \/ CompleteService(w)

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------

(************)
(* Fairness *)
(************)

(* Under weak fairness on each worker's actions, every queued customer *)
(* is eventually served. Without fairness, workers could idle forever. *)
FairSpec == Spec /\ \A w \in Workers :
    /\ WF_vars(AssignWorker(w))
    /\ WF_vars(FinishPreparing(w))
    /\ WF_vars(CompleteService(w))

---------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

(* An idle worker has no customer; a busy worker always has one *)
IdleConsistency ==
    \A w \in Workers : workerState[w] = "Idle" <=> workerCustomer[w] = 0

(* No two workers handle the same customer simultaneously *)
NoDoubleAssignment ==
    \A w1, w2 \in Workers :
        w1 /= w2 /\ workerCustomer[w1] /= 0
        => workerCustomer[w1] /= workerCustomer[w2]

(* Every issued ticket is in exactly one logical state:              *)
(* queued (waiting), assigned (being prepared or served), or served. *)
TicketStatePartition ==
    LET assigned == { workerCustomer[w] : w \in { x \in Workers : workerCustomer[x] /= 0 } }
        queued   == Range(queue)
        issued   == 1..arrivals
    IN /\ queued \cup assigned \cup served = issued
       /\ queued \cap assigned = {}
       /\ queued \cap served   = {}
       /\ assigned \cap served = {}

(* The queue preserves FIFO order: earlier tickets always appear first *)
QueueOrdered ==
    \A i, j \in DOMAIN queue : i < j => queue[i] < queue[j]

---------------------------------------------------------------------------

(* State constraint for bounding model checking; not part of the spec. *)
StateConstraint == arrivals <= MaxArrivals

---------------------------------------------------------------------------

THEOREM Spec => []TypeOK
THEOREM Spec => []IdleConsistency
THEOREM Spec => []NoDoubleAssignment
THEOREM Spec => []TicketStatePartition
THEOREM Spec => []QueueOrdered

=============================================================================

