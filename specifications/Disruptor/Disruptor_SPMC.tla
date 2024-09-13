----------------------------- MODULE Disruptor_SPMC -------------------------
(***************************************************************************)
(* Models a Single Producer, Multi Consumer Disruptor (SPMC).              *)
(*                                                                         *)
(* The model verifies that no data races occur between the publisher       *)
(* and consumers and that all consumers eventually read all published      *)
(* values.                                                                 *)
(*                                                                         *)
(* To see a data race, try and run the model with two publishers.          *)
(***************************************************************************)

EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS
  Writers,      (* Writer/publisher thread ids.    *)
  Readers,      (* Reader/consumer  thread ids.    *)
  MaxPublished, (* Max number of published events. *)
  Size,         (* Ringbuffer size.                *)
  NULL

VARIABLES
  ringbuffer,
  published,    (* Publisher Cursor.                           *)
  read,         (* Read Cursors. One per consumer.             *)
  consumed,     (* Sequence of all read events by the Readers. *)
  pc            (* Program Counter of each Writer/Reader.      *)

vars == <<
  ringbuffer,
  published,
  read,
  consumed,
  pc
>>

(***************************************************************************)
(* Each publisher/consumer can be in one of two states:                    *)
(* 1. Accessing a slot in the Disruptor or                                 *)
(* 2. Advancing to the next slot.                                          *)
(***************************************************************************)
Access  == "Access"
Advance == "Advance"

Transition(t, from, to) ==
  /\ pc[t] = from
  /\ pc'   = [ pc EXCEPT ![t] = to ]

Buffer  == INSTANCE RingBuffer

Range(f) ==
  { f[x] : x \in DOMAIN(f) }

MinReadSequence ==
  CHOOSE min \in Range(read) : \A r \in Readers : min <= read[r]

(***************************************************************************)
(* Publisher Actions:                                                      *)
(***************************************************************************)

BeginWrite(writer) ==
  LET
    next     == published + 1
    index    == Buffer!IndexOf(next)
    min_read == MinReadSequence
  IN
    \* Are we clear of all consumers? (Potentially a full cycle behind).
    /\ min_read >= next - Size
    /\ next < MaxPublished
    /\ Transition(writer, Access, Advance)
    /\ Buffer!Write(index, writer, next)
    /\ UNCHANGED << consumed, published, read >>

EndWrite(writer) ==
  LET
    next  == published + 1
    index == Buffer!IndexOf(next)
  IN
    /\ Transition(writer, Advance, Access)
    /\ Buffer!EndWrite(index, writer)
    /\ published' = next
    /\ UNCHANGED << consumed, read >>

(***************************************************************************)
(* Consumer Actions:                                                       *)
(***************************************************************************)

BeginRead(reader) ==
  LET
    next  == read[reader] + 1
    index == Buffer!IndexOf(next)
  IN
    /\ published >= next
    /\ Transition(reader, Access, Advance)
    /\ Buffer!BeginRead(index, reader)
    \* Track what we read from the ringbuffer.
    /\ consumed' = [ consumed EXCEPT ![reader] = Append(@, Buffer!Read(index)) ]
    /\ UNCHANGED << published, read >>

EndRead(reader) ==
  LET
    next  == read[reader] + 1
    index == Buffer!IndexOf(next)
  IN
    /\ Transition(reader, Advance, Access)
    /\ Buffer!EndRead(index, reader)
    /\ read' = [ read EXCEPT ![reader] = next ]
    /\ UNCHANGED << consumed, published >>

(***************************************************************************)
(* Spec:                                                                   *)
(***************************************************************************)

Init ==
  /\ Buffer!Init
  /\ published = -1
  /\ read      = [ r \in Readers                |-> -1     ]
  /\ consumed  = [ r \in Readers                |-> << >>  ]
  /\ pc        = [ a \in Writers \union Readers |-> Access ]

Next ==
  \/ \E w \in Writers : BeginWrite(w)
  \/ \E w \in Writers : EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)
  \/ \E r \in Readers : EndRead(r)

Fairness ==
  /\ \A w \in Writers : WF_vars(BeginWrite(w))
  /\ \A w \in Writers : WF_vars(EndWrite(w))
  /\ \A r \in Readers : WF_vars(BeginRead(r))
  /\ \A r \in Readers : WF_vars(EndRead(r))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Invariants:                                                             *)
(***************************************************************************)

TypeOk ==
  /\ Buffer!TypeOk
  /\ published \in Int
  /\ read      \in [ Readers                -> Int                 ]
  /\ consumed  \in [ Readers                -> Seq(Nat)            ]
  /\ pc        \in [ Writers \union Readers -> { Access, Advance } ]

NoDataRaces == Buffer!NoDataRaces

(***************************************************************************)
(* Properties:                                                             *)
(***************************************************************************)

Liveliness ==
  <>[] (\A r \in Readers : consumed[r] = [i \in 1..MaxPublished |-> i - 1])

=============================================================================
