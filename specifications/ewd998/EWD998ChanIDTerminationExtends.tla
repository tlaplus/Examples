------------------- MODULE EWD998ChanIDTerminationExtends -------------------
(***************************************************************************)
(* This spec has the following notable differences compared to EWDChanID:  *)
(*  - Add SendTermination and RecvTermination actions that model how the   *)
(*    Initiator notifies the ring about final termination.                 *)
(*  - Introduce a new message type TrmMsg that the initiator sends to      *)
(*    notify the other nodes about termination. Here, the initiator        *)
(*    sends N-1 messages (one to each node), but an implementation could   *)
(*    e.g. use a broadcast or multicast (which would make for a nice       *)
(*    example at the PlusPy level)                                         *)
(*                                                                         *) 
(* Minor/Hack:                                                             *)
(*  - Hacks TypeOK to account for the set of Messages having changed       *)
(*    without being included in the refinement mapping.                    *)
(***************************************************************************)
EXTENDS EWD998ChanID

\* Declare and define a new message type.
TrmMsg == [type |-> "trm"]
TMessage == Message \cup {TrmMsg}

------------------------------------------------------------------------------

(*  *)
SendTermination(n) ==
  /\ n = Initiator
  /\ active[Initiator] = FALSE
  /\ color[Initiator] = "white"
  \* Don't send termination message multiple times determined by looking at
  \* global state (an actual implementation obviously won't need this).
  /\ \A j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type # "trm"
  /\ \E j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type = "tok"
        /\ inbox[n][j].color = "white"
        /\ counter[Initiator] + inbox[n][j].q = 0
        \* Don't remove the token msg from inbox[Initiator]
        \* because it would mess up Inv, i.e. tpos.
\*        /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ]
  \* Send termination message to all nodes (including self).
  /\ inbox' = [ node \in Nodes |-> inbox[node] \o <<TrmMsg>>]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, color, counter>>                            

(* Override with Sys.exit in PlusPy to gracefully terminate the runtime. *)
Terminate(n) == TRUE \*PrintT("sys.exit")

(*  *)
RecvTermination(n) ==
  /\ \E j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type = "trm"
  /\ Terminate(n)
  /\ UNCHANGED vars

Termination(n) ==
  \/ SendTermination(n) 
  \/ RecvTermination(n)
  
------------------------------------------------------------------------------

TTypeOK ==
  /\ TypeOK!1
  /\ TypeOK!2
  /\ TypeOK!3
  \* Seq(Messages) fails because we can't subst EWD998ChanID!Message
  \* with TMessage above (to do that we'd have to *refine* EWD998ChanID).
\*  /\ TypeOK!4
  /\ inbox \in [Nodes -> Seq(TMessage)]
  /\ TypeOK!5

TSystem(n) ==
  IF n = Initiator
     THEN InitiateProbe
     ELSE PassToken(n)

TEnvironment(n) ==
  \/ SendMsg(n) \/ RecvMsg(n) \/ Deactivate(n)

\* We want the existential at the outermost level because of how PlusPy
\* maps the actual/physical nodes to the logical spec nodes.
TNext(n) ==
  \/ TSystem(n)
  \/ TEnvironment(n) 
  \/ Termination(n)

TSpec ==
  Init /\ [][\E n \in Nodes: TNext(n)]_vars
       /\ \A n \in Nodes:
           /\ WF_vars(TSystem(n))
           /\ WF_vars(TEnvironment(n))
           /\ WF_vars(Termination(n))

THEOREM TSpec => Inv \* This is EWD998Chan!Inv all the way up.

------------------------------------------------------------------------------

\* Iff termination is detected by EWD998, there are no payload messages
\* in any node's inbox.
InvA ==
  EWD998!terminationDetected =>
        \A n \in Nodes: 
           \A msg \in Range(inbox[n]):
              msg.type # "pl"

\* Iff there is a termination message in any node's inbox, there are no
\* payload messages in any inbox.
InvB ==
  (\E n \in Nodes: 
    \E msg \in Range(inbox[n]): msg.type = "trm")
  =>
  (\A n2 \in Nodes:
    \A msg2 \in Range(inbox[n2]): msg2.type # "pl")

THEOREM TSpec => (InvB /\ InvA)

\* TerminationMessages does *not* hold because nodes can keep
\* sending (payload) messages indefinitely.
TerminationMessages ==
  <>[][\A n \in Nodes : RecvTermination(n)]_vars

\* Iff - from some point onward - none of the nodes send out
\* payload messages, all nodes will eventually terminate.
TerminationMessagesIfNoPayloadMessages ==
  <>[][\A n \in Nodes : ~ SendMsg(n)]_vars =>
               <>[][\A n \in Nodes : RecvTermination(n)]_vars

THEOREM TSpec => TerminationMessagesIfNoPayloadMessages
=============================================================================
