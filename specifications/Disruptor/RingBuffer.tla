----------------------------- MODULE RingBuffer -----------------------------
(***************************************************************************)
(* Models a Ring Buffer where each slot can contain an integer.            *)
(* Initially all slots contains NULL.                                      *)
(*                                                                         *)
(* Read and write accesses to each slot are tracked to detect data races.  *)
(* This entails that each write and read of a slot has multiple steps.     *)
(*                                                                         *)
(* All models using the RingBuffer should assert the NoDataRaces invariant *)
(* that checks against data races between multiple producer threads and    *)
(* consumer threads.                                                       *)
(***************************************************************************)

LOCAL INSTANCE Naturals
LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets

CONSTANTS
  Size,
  Readers,
  Writers,
  NULL

VARIABLE ringbuffer

LastIndex == Size - 1

(* Initial state of RingBuffer. *)
Init ==
  ringbuffer = [
    slots   |-> [i \in 0 .. LastIndex |-> NULL ],
    readers |-> [i \in 0 .. LastIndex |-> {}   ],
    writers |-> [i \in 0 .. LastIndex |-> {}   ]
  ]

(* The index into the Ring Buffer for a sequence number.*)
IndexOf(sequence) ==
  sequence % Size

(***************************************************************************)
(* Write operations.                                                       *)
(***************************************************************************)

Write(index, writer, value) ==
  ringbuffer' = [
    ringbuffer EXCEPT
      !.writers[index] = @ \union { writer },
      !.slots[index]   = value
  ]

EndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ { writer } ]

(***************************************************************************)
(*  Read operations.                                                       *)
(***************************************************************************)

BeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \union { reader } ]

Read(index) ==
  ringbuffer.slots[index]

EndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ { reader } ]

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)

TypeOk ==
  ringbuffer \in [
    slots:   UNION { [0 .. LastIndex -> Int \union { NULL }] },
    readers: UNION { [0 .. LastIndex -> SUBSET(Readers)    ] },
    writers: UNION { [0 .. LastIndex -> SUBSET(Writers)    ] }
  ]

NoDataRaces ==
  \A i \in 0 .. LastIndex :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

=============================================================================
