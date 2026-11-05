---------------------- MODULE EWD998ChanIDTermination ----------------------
(***************************************************************************)
(* This spec has the following two notable differences:                    *)
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
EXTENDS Integers, Sequences, FiniteSets, Naturals, Utils


CONSTANT Nodes
ASSUME IsFiniteSet(Nodes) /\ Nodes # {}

N == Cardinality(Nodes)

\* Choose a node to be the initiator of a fresh token. We don't care which one it
\* is as long as it is always the same.
Initiator == CHOOSE n \in Nodes : TRUE
                                         
\* Organize Nodes in a ring. 
RingOfNodes == 
  CHOOSE r \in [ Nodes -> Nodes ]: IsSimpleCycle(Nodes, r)

Color == {"white", "black"}

VARIABLES 
 active,
 color,
 counter,
 inbox
  
vars == <<active, color, counter, inbox>>

EWD998ChanID == INSTANCE EWD998ChanID \* Straight forward refinement mapping
                                      \* because we only *add* functionality.
                                      
\* Define a new message type.
TrmMsg == [type |-> "trm"]

\* Wow, this is ugly!  It would be cleaner to declare a Message constant in
\* EWD998, but that would mean that its definition has to happen in a TLC
\* model for model checking.  A TLC model cannot reference the definitions
\* of TokenMsg and BasicMsg in EWD998.
\*Message == {EWD998ChanID!EWD998Chan!TokenMsg, 
\*              EWD998ChanID!EWD998Chan!BasicMsg,
\*              TrmMsg}
\*
\*\* Poor mans re-define of TypeOK here because we re-defined Message above.
\*TypeOK ==
\*  /\ EWD998ChanID!EWD998Chan!TypeOK
\*  /\ inbox \in [Nodes -> Seq(Message)]
\*
\* Instead of the hacks above, I've used TLC's definition override to hack
\* TrmMsg into Messages:
\* Message[EWD998ChanId] <- 
\*       {EWD998ChanID!EWD998Chan!TokenMsg,  EWD998ChanID!EWD998Chan!BasicMsg, TrmMsg} 
\* This lets us check TypeOK and Inv.

------------------------------------------------------------------------------
 
Init ==
  (* Rule 0 *)
  /\ counter = [n \in Nodes |-> 0] \* c properly initialized
  /\ inbox = [n \in Nodes |-> IF n = Initiator 
                              THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
                              ELSE <<>>] \* with empty channels.
  (* EWD840 *) 
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]

InitiateProbe ==
  /\ \A j \in 1..Len(inbox[Initiator]) : 
        /\ inbox[Initiator][j].type # "trm"
  (* Rule 1 *)
  /\ \E j \in 1..Len(inbox[Initiator]):
      \* Token is at node the Initiator.
      /\ inbox[Initiator][j].type = "tok"
      /\ \* Previous round inconsistent, if:
         \/ inbox[Initiator][j].color = "black"
         \/ color[Initiator] = "black"
         \* Implicit stated in EWD998 as c0 + q > 0 means that termination has not 
         \* been achieved: Initiate a probe if the token's color is white but the
         \* number of in-flight messages is not zero.
         \/ counter[Initiator] + inbox[Initiator][j].q # 0
      /\ inbox' = [inbox EXCEPT ![RingOfNodes[Initiator]] = Append(@, 
           [type |-> "tok", q |-> 0,
             (* Rule 6 *)
             color |-> "white"]), 
             ![Initiator] = RemoveAt(@, j) ] \* consume token message from inbox[0]. 
  (* Rule 6 *)
  /\ color' = [ color EXCEPT ![Initiator] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            
  
PassToken(n) ==
  (* Rule 2 *)
  /\ ~ active[n] \* If machine i is active, keep the token.
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "tok"
          \* the machine nr.i+1 transmits the token to machine nr.i under q := q + c[i+1]
          /\ LET tkn == inbox[n][j]
             IN  inbox' = [inbox EXCEPT ![RingOfNodes[n]] = 
                                       Append(@, [tkn EXCEPT !.q = tkn.q + counter[n],
                                                             !.color = IF color[n] = "black"
                                                                       THEN "black"
                                                                       ELSE tkn.color]),
                                    ![n] = RemoveAt(@, j) ] \* pass on the token.
  (* Rule 7 *)
  /\ color' = [ color EXCEPT ![n] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            

System(n) == \/ /\ n = Initiator
                /\ InitiateProbe
             \/ /\ n # Initiator
                /\ PassToken(n)

-----------------------------------------------------------------------------

SendMsg(n) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[n]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Nodes \ {n} :
          \* Send a message (not the token) to j.
          /\ inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl" ] ) ]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color>>                            

\* RecvMsg could write the incoming message to a (Java) buffer from which the (Java) implementation consumes it. 
RecvMsg(n) ==
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![n] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![n] = "black" ]
  \* Receipt of a message activates node n.
  /\ active' = [ active EXCEPT ![n] = TRUE ]
  \* Consume a message (not the token!).
  /\ \E j \in 1..Len(inbox[n]) : 
          /\ inbox[n][j].type = "pl"
          /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ]
  /\ UNCHANGED <<>>                           

Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment(n) == 
  \/ SendMsg(n)
  \/ RecvMsg(n)
  \/ Deactivate(n)

-----------------------------------------------------------------------------

(*  *)
SendTermination ==
  \* Don't send termination message multiple times.  If - due to a
  \* cosmic ray - the initiator doesn't correctly terminate, don't
  \* let it interfere with future systems... 
  /\ \A j \in 1..Len(inbox[Initiator]) : 
        /\ inbox[Initiator][j].type # "trm"
  \* Safra's termination conditions:
  /\ active[Initiator] = FALSE
  /\ color[Initiator] = "white"
  /\ \E j \in 1..Len(inbox[Initiator]) : 
        /\ inbox[Initiator][j].type = "tok"
        /\ inbox[Initiator][j].color = "white"
        /\ counter[Initiator] + inbox[Initiator][j].q = 0
        \* Don't remove the token msg from inbox[Initiator]
        \* because it would mess up Inv, i.e. tpos.
\*        /\ inbox' = [inbox EXCEPT ![n] = RemoveAt(@, j) ]
  \* Send termination message to all nodes (including self).
  /\ inbox' = [ node \in Nodes |-> inbox[node] \o <<TrmMsg>>]
  \* TODO: Doesn't this re-enable the InitiateProbe action above?
  \* Account for the new messages sent.
  /\ counter' = [counter EXCEPT ![Initiator] = N]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, color>>                            

(* Override with Sys.exit in PlusPy to gracefully terminate the runtime. *)
Terminate(n) == TRUE \*PrintT("sys.exit")

(*  *)
RecvTermination(n) ==
  /\ \E j \in 1..Len(inbox[n]) : 
        /\ inbox[n][j].type = "trm"
  /\ Terminate(n)
  /\ UNCHANGED vars

Termination(n) ==
  \/ /\ n = Initiator
     /\ SendTermination
  \/ /\ n # Initiator
     /\ RecvTermination(n)
  
------------------------------------------------------------------------------

Next(n) ==
  \/ System(n)
  \/ Environment(n) 
  \/ Termination(n)

Spec ==
  Init /\ [][\E n \in Nodes: Next(n)]_vars
       /\ \A n \in Nodes:
           /\ WF_vars(System(n))
           /\ WF_vars(Environment(n))
           /\ WF_vars(Termination(n))

------------------------------------------------------------------------------

\* Iff - from some point onward - none of the nodes send out
\* payload messages, all nodes will eventually terminate.
TerminationMessagesIfNoPayloadMessages ==
  <>[][\A n \in Nodes : ~ SendMsg(n)]_vars =>
               <>[][\A n \in Nodes : RecvTermination(n)]_vars

THEOREM Spec => TerminationMessagesIfNoPayloadMessages

=============================================================================
