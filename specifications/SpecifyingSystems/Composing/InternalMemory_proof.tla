------------------------- MODULE InternalMemory_proof ----------------------
(***************************************************************************)
(* TLAPS proof of                                                          *)
(*                                                                         *)
(*    THEOREM ISpec => []TypeInvariant                                     *)
(*                                                                         *)
(* stated in InternalMemory.tla.                                           *)
(*                                                                         *)
(* TypeInvariant alone is not inductive: in Do(p), the next-state          *)
(* expression accesses buf[p].adr / buf[p].op, which only makes sense      *)
(* when buf[p] is in MReq.  We strengthen TypeInvariant with               *)
(* BufConsistent, which records the buf typing for each value of ctl[p].  *)
(***************************************************************************)
EXTENDS InternalMemory, TLAPS

BufConsistent ==
  /\ \A p \in Proc : (ctl[p] = "rdy")  => (buf[p] \in Val \cup {NoVal})
  /\ \A p \in Proc : (ctl[p] = "busy") => (buf[p] \in MReq)
  /\ \A p \in Proc : (ctl[p] = "done") => (buf[p] \in Val \cup {NoVal})

Inv == TypeInvariant /\ BufConsistent

LEMMA InvInductive == ISpec => []Inv
<1>1. IInit => Inv
  BY DEF IInit, Inv, TypeInvariant, BufConsistent
<1>2. Inv /\ [INext]_<<memInt, mem, ctl, buf>> => Inv'
  <2> SUFFICES ASSUME Inv,
                      [INext]_<<memInt, mem, ctl, buf>>
               PROVE  Inv'
    OBVIOUS
  <2>. USE DEF Inv, TypeInvariant, BufConsistent
  <2>1. ASSUME NEW p \in Proc, Req(p)
        PROVE  Inv'
    \* After Req(p): ctl[p]' = "busy", buf[p]' \in MReq.  For q # p,
    \* ctl/buf unchanged.  mem unchanged.
    BY <2>1 DEF Req
  <2>2. ASSUME NEW p \in Proc, Do(p)
        PROVE  Inv'
    \* Pre: ctl[p] = "busy", so buf[p] \in MReq, hence buf[p].adr \in Adr,
    \* and buf[p].op \in {"Rd","Wr"}.
    <3>1. buf[p] \in MReq
      BY <2>2 DEF Do
    <3>2. buf[p].adr \in Adr /\ buf[p].op \in {"Rd","Wr"}
      BY <3>1 DEF MReq
    <3>3. CASE buf[p].op = "Wr"
      \* mem' \in [Adr->Val] because we update at adr \in Adr to val \in Val.
      \* buf[p]' = NoVal \in Val \cup {NoVal}, ctl[p]' = "done".
      <4>1. buf[p].val \in Val
        BY <3>1, <3>3 DEF MReq
      <4>2. mem' = [mem EXCEPT ![buf[p].adr] = buf[p].val]
        BY <2>2, <3>3 DEF Do
      <4>3. mem' \in [Adr -> Val]
        BY <3>2, <4>1, <4>2
      <4>. QED  BY <2>2, <3>3, <4>3 DEF Do
    <3>4. CASE buf[p].op = "Rd"
      \* mem' = mem.  buf[p]' = mem[buf[p].adr] \in Val.  ctl[p]' = "done".
      <4>1. mem' = mem
        BY <2>2, <3>4 DEF Do
      <4>2. mem[buf[p].adr] \in Val
        BY <3>2
      <4>. QED  BY <2>2, <3>4, <4>1, <4>2 DEF Do
    <3>. QED  BY <3>2, <3>3, <3>4
  <2>3. ASSUME NEW p \in Proc, Rsp(p)
        PROVE  Inv'
    \* ctl[p]' = "rdy"; buf, mem unchanged.  buf[p] was \in Val \cup {NoVal}
    \* (since pre ctl[p] = "done"), so it remains so under "rdy".
    BY <2>3 DEF Rsp
  <2>4. CASE UNCHANGED <<memInt, mem, ctl, buf>>
    BY <2>4
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4 DEF INext
<1>. QED  BY <1>1, <1>2, PTL DEF ISpec

THEOREM TypeCorrect == ISpec => []TypeInvariant
BY InvInductive, PTL DEF Inv

============================================================================
