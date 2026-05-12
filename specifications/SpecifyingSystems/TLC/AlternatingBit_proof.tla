------------------------ MODULE AlternatingBit_proof -----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*   THEOREM ABSpec => []ABTypeInv                                         *)
(* stated in AlternatingBit.tla.                                           *)
(***************************************************************************)
EXTENDS AlternatingBit, TLAPS

LEMMA AppendType ==
  ASSUME NEW T, NEW s \in Seq(T), NEW e \in T
  PROVE  Append(s, e) \in Seq(T)
  OBVIOUS

LEMMA TailType ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Tail(s) \in Seq(T)
  OBVIOUS

LEMMA HeadType ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Head(s) \in T
  OBVIOUS

LEMMA LosePreservesType ==
  ASSUME NEW T, NEW q \in Seq(T), q # << >>,
         NEW i \in 1..Len(q),
         NEW q2,
         q2 = [j \in 1..(Len(q)-1) |-> IF j < i THEN q[j] ELSE q[j+1]]
  PROVE  q2 \in Seq(T)
  OBVIOUS

THEOREM TypeCorrect == ABSpec => []ABTypeInv
<1>1. ABInit => ABTypeInv
  BY DEF ABInit, ABTypeInv
<1>2. ABTypeInv /\ [ABNext]_abvars => ABTypeInv'
  <2> SUFFICES ASSUME ABTypeInv, [ABNext]_abvars
               PROVE  ABTypeInv'
    OBVIOUS
  <2>. USE DEF ABTypeInv
  <2>1. ASSUME NEW d \in Data, SndNewValue(d)
        PROVE  ABTypeInv'
    \* msgQ' = Append(msgQ, <<sBit', d>>); sBit' \in {0,1}, d \in Data,
    \* so <<sBit', d>> \in {0,1} \X Data; AppendType.
    BY <2>1, AppendType DEF SndNewValue
  <2>2. CASE ReSndMsg
    BY <2>2, AppendType DEF ReSndMsg
  <2>3. CASE RcvMsg
    BY <2>3, TailType, HeadType DEF RcvMsg
  <2>4. CASE SndAck
    BY <2>4, AppendType DEF SndAck
  <2>5. CASE RcvAck
    BY <2>5, TailType, HeadType DEF RcvAck
  <2>6. CASE LoseMsg
    BY <2>6, LosePreservesType DEF LoseMsg, Lose
  <2>7. CASE LoseAck
    BY <2>7, LosePreservesType DEF LoseAck, Lose
  <2>8. CASE UNCHANGED abvars
    BY <2>8 DEF abvars
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF ABNext
<1>. QED  BY <1>1, <1>2, PTL DEF ABSpec

============================================================================
