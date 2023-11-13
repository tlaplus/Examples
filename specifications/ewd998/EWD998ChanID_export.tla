
This modules demonstrates how to integrate TLC with third-party tools by
exporting counter-examples/error-traces.  You can ignore  MCInit  and  RealInv  
and skip to  JsonInv  and  PostInv.

Run TLC in simulations/generator mode to quickly violate  RealInv  :

$ tlc -generate -noTE EWD998ChanID_export

------------------------ MODULE EWD998ChanID_export ------------------------
EXTENDS EWD998ChanID, TLCExt, TLC, IOUtils, Json

MCInit ==
  (* Rule 0 *)
  /\ counter = [n \in Node |-> 0] \* c properly initialized
  /\ inbox = [n \in Node |-> IF n = Initiator 
                              THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
                              ELSE <<>>] \* with empty channels.
  (* EWD840 *)
  \* Reduce the number of initial states. 
  /\ active \in [Node -> {TRUE}]
  /\ color \in [Node -> {"white"}]
  (* Each node maintains a (local) vector clock *)
  (* https://en.wikipedia.org/wiki/Vector_clock *)
  /\ clock = [n \in Node |-> [m \in Node |-> 0] ]

----------------------------------------------------------------------------

RealInv ==
    \* Some read-world invariant (here terminationDetected occurs within N steps
     \* where N has been chosen arbitrarily).
    EWD998Chan!EWD998!terminationDetected => TLCGet("level") < 23

----------------------------------------------------------------------------

(* Format the error-trace as JSON and write to a file. *)

JsonInv ==
    \/ RealInv
    \/ /\ JsonSerialize("EWD998ChanID_export.json", Trace)
       /\ Print("JSON trace written to EWD998ChanID_export.json",
                 FALSE) \* Make TLC stop and print the usual error trace.

----------------------------------------------------------------------------

(* Format the error-trace as JSON and ping some web endpoint. *)

Curl ==
    <<"curl", "-H", "Content-Type:application/json", 
    "-X", "POST", "-d", "%s", "https://postman-echo.com/post">>

PostInv ==
    \/ RealInv
    \/ Print(
        IOExecTemplate(Curl, <<ToJsonObject(Trace)>>).stdout, 
            FALSE) \* Make TLC stop and print the usual error trace.

=============================================================================