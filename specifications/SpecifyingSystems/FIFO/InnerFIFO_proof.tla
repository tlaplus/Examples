------------------------- MODULE InnerFIFO_proof ---------------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM Spec => []TypeInvariant                                       *)
(* stated in InnerFIFO.tla.                                                *)
(***************************************************************************)
EXTENDS InnerFIFO, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
<1>1. Init => TypeInvariant
  BY DEF Init, TypeInvariant,
         InChan!Init, OutChan!Init,
         InChan!TypeInvariant, OutChan!TypeInvariant
<1>2. TypeInvariant /\ [Next]_<<in, out, q>> => TypeInvariant'
  <2> SUFFICES ASSUME TypeInvariant, [Next]_<<in, out, q>>
               PROVE  TypeInvariant'
    OBVIOUS
  <2>. USE DEF TypeInvariant, InChan!TypeInvariant, OutChan!TypeInvariant
  <2>1. ASSUME NEW msg \in Message, SSend(msg)
        PROVE  TypeInvariant'
    BY <2>1 DEF SSend, InChan!Send
  <2>2. CASE BufRcv
    BY <2>2 DEF BufRcv, InChan!Rcv
  <2>3. CASE BufSend
    \* OutChan!Send(Head(q)) requires Head(q) \in Message; q \in Seq(Message)
    \* and q # <<>>, so Head(q) \in Message.
    BY <2>3 DEF BufSend, OutChan!Send
  <2>4. CASE RRcv
    BY <2>4 DEF RRcv, OutChan!Rcv
  <2>5. CASE UNCHANGED <<in, out, q>>
    BY <2>5
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

============================================================================
