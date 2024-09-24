--------------------------- MODULE Disruptor_MPMC --------------------------
(***************************************************************************)
(* Models a Multi Producer, Multi Consumer Disruptor (MPMC).               *)
(*                                                                         *)
(* The producers publish their claimed sequence number as value into       *)
(* the RingBuffer and the model verifies that all consumers read all       *)
(* published values.                                                       *)
(*                                                                         *)
(* The model also verifies that no data races occur between the producers  *)
(* and consumers and that all consumers eventually read all published      *)
(* values (in a Multicast fashion - i.e. all consumers read all events).   *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  MaxPublished,     (* Max number of published events. Bounds the model.    *)
  Writers,          (* Writer/producer thread ids.                          *)
  Readers,          (* Reader/consumer thread ids.                          *)
  Size,             (* Ringbuffer size.                                     *)
  NULL

ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME Size         \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}

VARIABLES
  ringbuffer,
  next_sequence,    (* Shared counter for claiming a sequence for a Writer. *)
  claimed_sequence, (* Claimed sequence by each Writer.                     *)
  published,        (* Encodes whether each slot is published.              *)
  read,             (* Read Cursors. One per Reader.                        *)
  pc,               (* Program Counter for each Writer/Reader.              *)
  consumed          (* Sequence of all read events by the Readers.          *)
                    (* This is a history variable used for liveliness       *)
                    (* checking.                                            *)

vars == <<
  ringbuffer,
  next_sequence,
  claimed_sequence,
  published,
  read,
  consumed,
  pc
>>

(***************************************************************************)
(* Each producer/consumer can be in one of two states:                     *)
(* 1. Accessing a slot in the Disruptor or                                 *)
(* 2. Advancing to the next slot.                                          *)
(***************************************************************************)
Access  == "Access"
Advance == "Advance"

Transition(t, from, to) ==
  /\ pc[t] = from
  /\ pc'   = [ pc EXCEPT ![t] = to ]

Buffer == INSTANCE RingBuffer WITH Values <- Int

Xor(A, B) == A = ~B

Range(f) ==
  { f[x] : x \in DOMAIN(f) }

MinReadSequence ==
  CHOOSE min \in Range(read) :
    \A r \in Readers : min <= read[r]

MinClaimedSequence ==
  CHOOSE min \in Range(claimed_sequence) :
    \A w \in Writers : min <= claimed_sequence[w]

(***************************************************************************)
(* Encode whether an index is published by tracking if the slot was        *)
(* published in an even or odd index. This works because producers         *)
(* cannot overtake consumers.                                              *)
(***************************************************************************)
IsPublished(sequence) ==
  LET
    index   == Buffer!IndexOf(sequence)
    \* Round number starts at 0.
    round   == sequence \div Size
    is_even == round % 2 = 0
  IN
    \* published[index] is true if published in an even round otherwise false
    \* as it was published in an odd round number.
    published[index] = is_even

Publish(sequence) ==
  LET index == Buffer!IndexOf(sequence)
  \* Flip whether we're at an even or odd round.
  IN  published' = [ published EXCEPT ![index] = Xor(TRUE, @) ]

(***************************************************************************)
(* Computes the highest published sequence number that can be read.        *)
(* This might seem strange but e.g. a producer P1 can be about to publish  *)
(* sequence 5 while producer P2 has published sequence 6 and thus          *)
(* consumers can neither read sequence 5 nor 6 (yet).                      *)
(***************************************************************************)
AvailablePublishedSequence ==
  LET guaranteed_published == MinClaimedSequence - 1
      candidate_sequences  == {guaranteed_published} \union Range(claimed_sequence)
  IN  CHOOSE max \in candidate_sequences :
        IsPublished(max) => ~ \E w \in Writers :
          /\ claimed_sequence[w] = max + 1
          /\ IsPublished(claimed_sequence[w])

(***************************************************************************)
(* Producer Actions:                                                       *)
(***************************************************************************)

BeginWrite(writer) ==
  LET
    seq      == next_sequence
    index    == Buffer!IndexOf(seq)
    min_read == MinReadSequence
  IN
    \* Are we clear of all consumers? (Potentially a full cycle behind).
    /\ min_read >= seq - Size
    /\ claimed_sequence' = [ claimed_sequence EXCEPT ![writer] = seq ]
    /\ next_sequence'    = seq + 1
    /\ Transition(writer, Advance, Access)
    /\ Buffer!Write(index, writer, seq)
    /\ UNCHANGED << consumed, published, read >>

EndWrite(writer) ==
  LET
    seq   == claimed_sequence[writer]
    index == Buffer!IndexOf(seq)
  IN
    /\ Transition(writer, Access, Advance)
    /\ Buffer!EndWrite(index, writer)
    /\ Publish(seq)
    /\ UNCHANGED << claimed_sequence, next_sequence, consumed, read >>

(***************************************************************************)
(* Consumer Actions:                                                       *)
(***************************************************************************)

BeginRead(reader) ==
  LET
    next  == read[reader] + 1
    index == Buffer!IndexOf(next)
  IN
    /\ IsPublished(next)
    /\ Transition(reader, Advance, Access)
    /\ Buffer!BeginRead(index, reader)
    \* Track what we read from the ringbuffer.
    /\ consumed' = [ consumed EXCEPT ![reader] = Append(@, Buffer!Read(index)) ]
    /\ UNCHANGED << claimed_sequence, next_sequence, published, read >>

EndRead(reader) ==
  LET
    next  == read[reader] + 1
    index == Buffer!IndexOf(next)
  IN
    /\ Transition(reader, Access, Advance)
    /\ Buffer!EndRead(index, reader)
    /\ read' = [ read EXCEPT ![reader] = next ]
    /\ UNCHANGED << claimed_sequence, next_sequence, consumed, published >>

(***************************************************************************)
(* Spec:                                                                   *)
(***************************************************************************)

Init ==
  /\ Buffer!Init
  /\ next_sequence    = 0
  /\ claimed_sequence = [ w \in Writers                |-> -1      ]
  /\ published        = [ i \in 0..Buffer!LastIndex    |-> FALSE   ]
  /\ read             = [ r \in Readers                |-> -1      ]
  /\ consumed         = [ r \in Readers                |-> << >>   ]
  /\ pc               = [ a \in Writers \union Readers |-> Advance ]

Next ==
  \/ \E w \in Writers : BeginWrite(w)
  \/ \E w \in Writers : EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)
  \/ \E r \in Readers : EndRead(r)

Fairness ==
  /\ \A r \in Readers : WF_vars(BeginRead(r))
  /\ \A r \in Readers : WF_vars(EndRead(r))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* State constraint - bounds model:                                        *)
(***************************************************************************)

StateConstraint == next_sequence <= MaxPublished

(***************************************************************************)
(* Invariants:                                                             *)
(***************************************************************************)

NoDataRaces == Buffer!NoDataRaces

TypeOk ==
  /\ Buffer!TypeOk
  /\ next_sequence    \in Nat
  /\ claimed_sequence \in [ Writers                -> Int                 ]
  /\ published        \in [ 0..Buffer!LastIndex    -> { TRUE, FALSE }     ]
  /\ read             \in [ Readers                -> Int                 ]
  /\ consumed         \in [ Readers                -> Seq(Nat)            ]
  /\ pc               \in [ Writers \union Readers -> { Access, Advance } ]

(***************************************************************************)
(* Properties:                                                             *)
(***************************************************************************)

(* Eventually always, consumers must have read all published values.       *)
Liveliness ==
  \A r \in Readers : \A i \in 0..(MaxPublished - 1) :
    <>[](i \in 0..AvailablePublishedSequence => Len(consumed[r]) >= i + 1 /\ consumed[r][i + 1] = i)

=============================================================================
