----------------------------- MODULE RingBuffer -----------------------------
(***************************************************************************)
(* Models a RingBuffer where each slot can contain an element from         *)
(* Values. Initially all slots contains NULL.                              *)
(*                                                                         *)
(* Read and write accesses to each slot are tracked to detect data races.  *)
(* This entails that each write and read of a slot has multiple steps.     *)
(*                                                                         *)
(* All models using the RingBuffer should assert the NoDataRaces invariant *)
(* that checks against data races between multiple producer threads and    *)
(* consumer threads.                                                       *)
(***************************************************************************)

LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets

CONSTANTS
  Size,    (* The number of slots in the RingBuffer.                *)
  Readers, (* The set of readers to the RingBuffer.                 *)
  Writers, (* The set of writers to the RingBuffer.                 *)
  Values,  (* The set of values storable in the RingBuffer's slots. *)
  NULL

ASSUME Size \in Nat \ {0}
ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME NULL \notin Values

VARIABLE ringbuffer

(* Last index in the RingBuffer. *)
LastIndex == Size - 1

(***************************************************************************)
(* Clients using the RingBuffer must ensure there are no data races.       *)
(* I.e. NoDataRaces must be an invariant in the spec using the Ringbuffer. *)
(***************************************************************************)
NoDataRaces ==
  \A i \in 0 .. LastIndex :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

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
    slots:   UNION { [0 .. LastIndex -> Values \union { NULL }] },
    readers: UNION { [0 .. LastIndex -> SUBSET(Readers)       ] },
    writers: UNION { [0 .. LastIndex -> SUBSET(Writers)       ] }
  ]

=============================================================================
