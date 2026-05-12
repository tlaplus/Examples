--------------------------- MODULE Channel_proof ---------------------------
(***************************************************************************)
(* TLAPS proof of the theorem stated in Channel.tla.                       *)
(***************************************************************************)
EXTENDS Channel, TLAPS

THEOREM TypeCorrect == Spec => []TypeInvariant
<1>1. Init => TypeInvariant
  BY DEF Init
<1>2. TypeInvariant /\ [Next]_chan => TypeInvariant'
  BY DEF TypeInvariant, Next, Send, Rcv
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

============================================================================
