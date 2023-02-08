--------------------------- MODULE EWD998ChanTrace --------------------------
EXTENDS EWD998Chan, Json, TLC, IOUtils, VectorClocks

\* Trace validation has been designed for TLC running in default model-checking
 \* mode, i.e., breadth-first search.
ASSUME TLCGet("config").mode = "bfs"

JsonLog ==
    \* Deserialize the System log as a sequence of records from the log file.
     \* Run TLC with (assuming a suitable "tlc" shell alias):
     \* $ JSON=impl/EWD998ChanTrace-01.ndjson tlc -note EWD998ChanTrace
     \* Fall back to trace.ndjson if the JSON environment variable is not set.
    ndJsonDeserialize(IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "trace.ndjson")

TraceN ==
    \* The first line of the log statement has the number of nodes.
    JsonLog[1].N

TraceLog ==
    \* SubSeq starting at 2 to skip the N value.
    LET suffix == SubSeq(JsonLog, 2, Len(JsonLog))
    \* The JsonLog/Trace has been compiled out of several logs, collected from the
     \* nodes of the distributed system, and, thus, are unordered.
    IN CausalOrder(suffix, 
                    LAMBDA l : l.pkt.vc,
                    \* ToString is a hack to work around the fact that the Json
                     \* module deserializes {"0": 42, "1": 23} into the record
                     \* [ 0 |-> 42, 1 |-> 23 ] with domain {"0","1"} and not into
                     \* a function with domain {0, 1}.  This is a known issue of
                     \* the Json module. Consider switching to, e.g., EDN 
                     \* (https://github.com/edn-format/edn).
                    LAMBDA l : ToString(l.node), LAMBDA vc : DOMAIN vc)


-----------------------------------------------------------------------------

TraceInitConstraint ==
    \* The implementation's initial state is deterministic and known.
    TLCGet("level") = 1 => \A n \in Node: 
                                /\ active[n]
                                /\ color[n] = "white"
                                /\ counter[n] = 0

-----------------------------------------------------------------------------

PayloadPred(msg) ==
    msg.type = "pl"

\* Beware to only prime e.g. inbox in inbox'[rcv] and *not* also rcv, i.e.,
 \* inbox[rcv]'.  rcv is defined in terms of TLCGet("level") that correctly
 \* handles priming, which causes for rcv' to equal rcv of the next log line.

IsInitiateToken(l) ==
    \* Log statement was printed by the sender (initiator).
    /\ l.event = ">"
    /\ LET msg == l.pkt.msg 
           snd == l.pkt.snd 
           rcv == l.pkt.rcv IN
        \* Log statement is about a token message.
        /\ msg.type = "tok"
        \* Log statement show N-1 to be receiver and 0 to be the sender.
        /\ rcv = N - 1
        /\ snd = 0
        \* The senders's inbox contains a tok message in the current state.
        /\ \E idx \in DOMAIN inbox[snd]:
                inbox[snd][idx].type = "tok"
        \* The senders's inbox contains no longer the token in the next state.
        /\ \A idx \in DOMAIN inbox'[snd]:
                inbox'[snd][idx].type # "tok"
        \* Sender has *not* to be inactive to initiate the token!
        /\ UNCHANGED <<active, counter>>                            
    
IsPassToken(l) ==
    \* Log statement was printed by the sender.
    /\ l.event = ">"
    /\ LET msg == l.pkt.msg 
           snd == l.pkt.snd 
           rcv == l.pkt.rcv IN
        \* Log statement is about a token message.
        /\ msg.type = "tok"
        \* The sender's inbox contains a tok message in the current state.
        /\ \E idx \in DOMAIN inbox[snd]:
            /\ inbox[snd][idx].type = "tok"
            /\ inbox[snd][idx].q + counter[snd] = msg.q
            /\ msg.color = IF color[snd] = "black" 
                        THEN "black"
                        ELSE inbox[snd][idx].color
        \* The sender's inbox contains no tok message in the next state.
        /\ \A idx \in DOMAIN inbox'[snd]:
                inbox'[snd][idx].type # "tok"
        \* Sender has to be inactive to pass the token, i.e
        /\ ~active[snd]
        /\ UNCHANGED <<active, counter>>                            

IsSendMsg(l) ==
    \* Log statement was printed by the sender.
    /\ l.event = ">"
    /\ LET msg == l.pkt.msg 
           rcv == l.pkt.rcv
           snd == l.pkt.snd IN
        \* Log statement is about a payload message. 
        /\ msg.type = "pl"
        \* Sender has to be active to send a message.
        /\ active[snd]
        \* Sender increments its counter.
        /\ counter'[snd] = counter[snd] + 1
        \* The sender's inbox remains unchanged, bu the receivers's inbox contains one more
         \* pl message.  In the implementation, the message is obviously in flight, i.e. it 
         \* is send via the wire to the receiver.  However, the  SendMsg  action models it
         \* such that the message is atomically appended to the receiver's inbox. 
        /\ Len(SelectSeq(inbox[rcv], PayloadPred)) < Len(SelectSeq(inbox'[rcv], PayloadPred))
        /\ UNCHANGED <<active, color>>                            

IsRecvMsg(l) ==
    \* Log statement was printed by the receiver.
    /\ l.event = "<"
    /\ LET msg == l.pkt.msg 
           rcv == l.pkt.rcv IN
        \* Log statement is about a payload message.
        /\ msg.type = "pl"
        \* Receiving a message activates, decrements the counter, and changes the color of the
         \* receiver.
        /\ active' = [active EXCEPT ![rcv] = TRUE]
        /\ counter' = [counter EXCEPT ![rcv] = @ - 1]
        /\ color' = [ color EXCEPT ![rcv] = "black" ]
        \* Even though the name of the action suggests that there is one *more* pl message in
         \* the receiver's inbox, the action  RecvMsg  removes the pl message from the node's
         \* inbox.  Thus, thee receiver's inbox contains one less pl message in the next state.
        /\ Len(SelectSeq(inbox[rcv], PayloadPred)) > Len(SelectSeq(inbox'[rcv], PayloadPred))

TraceNextConstraint ==
    \* We could have used an auxiliary spec variable for i  , but TLCGet("level") has the
     \* advantage that TLC continues to show the high-level action names instead of just  Next.
     \* However, it is imparative to run TLC with the TraceView above configured as a VIEW in
     \* TLC's config file.  Otherwise, TLC will stop model checking when a high-level state
     \* appears a second time in the trace.
    LET i == TLCGet("level")
    IN \* Equals FALSE if we get past the end of the log, causing model checking to stop.
       /\ i <= Len(TraceLog)
       /\ LET logline == TraceLog[i]
          IN \* If the postcondition  TraceAccepted  is violated, adding a TLA+ debugger
              \* breakpoint with a hit count copied from TLC's error message on the 
              \* BP:: line below is the first step towards diagnosing a divergence. Once
              \* hit, advance evaluation with step over (F10) and step into (F11).
              BP::
                \/ IsInitiateToken(logline)
                \/ IsPassToken(logline)
                \/ IsSendMsg(logline)
                \/ IsRecvMsg(logline)

-----------------------------------------------------------------------------

TraceAccepted ==
    \* If the prefix of the TLA+ behavior is shorter than the trace, TLC will
     \* report a violation of this postcondition.  But why do we need a postcondition
     \* at all?  Couldn't we use an ordinary property such as
     \*  <>[](TLCGet("level") >= Len(TraceLog))  ?  The answer is that an ordinary
     \* property is true of a single behavior, whereas  TraceAccepted  is true of a
     \* set of behaviors; it is essentially a poor man's hyperproperty.
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Len(TraceLog) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:", TraceLog[d], 
                    "TLA+ debugger breakpoint hit count " \o ToString(d+1)>>, FALSE)

-----------------------------------------------------------------------------

TraceAlias ==
    \* The  TraceAlias  is nothing but a debugging aid.  Especially the enabled
     \* helped me figure out why a trace was not accepted.  In the TLA+ debugger,
     \* this  TraceAlias  can be entered as a "WATCH" expression.
    [
        \* TODO: Funny TLCGet("level")-1 could be removed if the spec has an
        \* TODO: auxiliary counter variable  i  .  Would also take care of 
        \* TODO: the bug that TLCGet("level")-1 is not defined for the initial
        \* TODO: state.
        log     |-> <<TLCGet("level"), TraceLog[TLCGet("level") - 1]>>,
        active  |-> active,
        color   |-> color,
        counter |-> counter,
        inbox   |-> inbox,
        term    |-> <<EWD998!terminationDetected, "=>", EWD998!Termination>>,
        enabled |-> 
            [
                InitToken  |-> ENABLED InitiateProbe,
                PassToken  |-> ENABLED \E i \in Node \ {0} : PassToken(i),
                SendMsg    |-> ENABLED \E i \in Node : SendMsg(i),
                RecvMsg    |-> ENABLED \E i \in Node : RecvMsg(i),
                Deactivate |-> ENABLED \E i \in Node : Deactivate(i)
            ]
    ]

=============================================================================

Tips & Tricks for writing TLA+ "trace specs"
--------------------------------------------

1.  If the postcondition  TraceAccepted  is violated, adding a TLA+ debugger
    breakpoint on the line  TraceAccepted!BP  with a hit count value copied from
    TLC's error message, is the first step towards diagnosing the divergence.
    a) In the TLA+ debugger, enter the  TraceAlias  as a "WATCH" expression.  
       Especially the  enabled  field helped me figure out why a trace was not
       accepted.
    b) Enter the  TraceLog  as another "WATCH" expression to show the trace log
       in the TLA+ debugger.  Remember, the trace log file may not be in vector
       clock order.

2.  A trace ideally maps to a single TLA+ behavior, but we may use non-determinism
    in the TLA+ trace spec to fill the holes of a partial/incomplete log, which can
    cause the trace to be mapped to multiple TLA+ behaviors.  A *buggy* trace spec
    is another reason why a trace is mapped to more than one behavior.  To find the
    states with multiple successor states, we found the following two techniques
    useful:
        a) The TLA+ debugger can be used to find states with multiple successor
           states.  Set *inline* breakpoints with a hit count of 2 on all actions
           of the high-level spec, or the actions suspected of having multiple
           successors.  The TLA+ debugger will stop at the first state with multiple
           successors.  An inline breakpoint is a breakpoint set on the right-hand
           side of an action definition, i.e., the  SendMsg  in the definition 
           SendMsg(i) == /\ ...
        b) For short traces, having TLC dump the state graph to a GraphViz file
           can be useful.  The GraphViz file can be generated by setting the
           -dump dot  option of TLC to a file name, e.g.,  -dump dot out.dot
           When combined with an ordinary breakpoint of the TLA+ debugger at the
           top of  TraceNextConstraint  , dumping the state graph with
           -dump dot,snapshot  will cause TLC to create a snapshot of the current
           state graph every time the TLA+ debugger stops at the breakpoint.


Shell snippets
--------------


$ alias tlc
tlc='java -cp /path/to/tla2tools.jar tlc2.TLC'

$ javac -cp impl/lib/gson-2.8.6.jar -d impl/bin impl/src/*.java
$ while true; do
    T=trace-$(date +%s).ndjson
    ## Generate a system trace and save if to trace.ndjson.
    java -cp impl/bin:impl/lib/gson-2.8.6.jar EWD998App 1 | tee $T
    ## Validate the system trace (break if the trace fails validation).
    JSON=$T tlc -noTE EWD998ChanTrace || break
    ## Remove T if the trace was accepted.
    rm $T
    ## Wait a few seconds for the OS to reclaim resources.
    sleep 3; 
  done

