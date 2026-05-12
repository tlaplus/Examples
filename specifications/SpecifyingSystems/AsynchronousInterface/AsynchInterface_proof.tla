------------------------ MODULE AsynchInterface_proof ----------------------
(***************************************************************************)
(* TLAPS proof of the theorem stated in AsynchInterface.tla.               *)
(***************************************************************************)
EXTENDS AsynchInterface, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
<1>1. Init => TypeInvariant
  BY DEF Init, TypeInvariant
<1>2. TypeInvariant /\ [Next]_<<val, rdy, ack>> => TypeInvariant'
  BY DEF TypeInvariant, Next, Send, Rcv
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

============================================================================
