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
    ndJsonDeserialize(IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "specifications/ewd998/EWD998ChanTrace.ndjson")

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

TraceInit ==
    /\ Init!1
    /\ Init!2
    \* We happen to know that in the implementation all nodes are initially empty and white.
    /\ active \in [Node -> {TRUE}]
    /\ color \in [Node -> {"white"}]

TraceSpec ==
    \* Because of  [A]_v <=> A \/ v=v'  , the following formula is logically
     \* equivalent to the (canonical) Spec formual  Init /\ [][Next]_vars  .  
     \* However, TLC's breadth-first algorithm does not explore successor
     \* states of a *seen* state.  Since one or more states may appear one or 
     \* more times in the the trace, the  UNCHANGED vars  combined with the
     \*  TraceView  that includes  TLCGet("level")  is our workaround. 
    TraceInit /\ [][Next \/ UNCHANGED vars]_vars

-----------------------------------------------------------------------------

PayloadPred(msg) ==
    msg.type = "pl"

\* Beware to only prime e.g. inbox in inbox'[rcv] and *not* also rcv, i.e.,
 \* inbox[rcv]'.  rcv is defined in terms of TLCGet("level") that correctly
 \* handles priming, which causes for rcv' to equal rcv of the next log line.

IsInitiateToken(l) ==
    \* Log statement was printed by the sender (initiator).
    /\ l.event = ">"
    \* Log statement is about a token message.
    /\ l.pkt.msg.type = "tok"
    \* Log statement show N-1 to be receiver and 0 to be the sender.
    /\ l.pkt.rcv = N - 1
    /\ l.pkt.snd = 0
    /\ <<InitiateProbe>>_vars
    
IsPassToken(l) ==
    \* Log statement was printed by the sender.
    /\ l.event = ">"
    \* Log statement is about a token message.
    /\ l.pkt.msg.type = "tok"
    /\ LET snd == l.pkt.snd IN
        \* The high-level spec precludes the initiator from passing the token in the
         \* the  System  formula by remove the initiator from the set of all nodes.  Here,
         \* we model this by requiring that the sender is not the initiator. 
        /\ l.pkt.snd > 0
        /\ <<PassToken(snd)>>_vars
    
\* Note that there is no corresponding sub-action in the high-level spec!  This constraint
 \* is true of any sub-action that appends a tok message to the receiver's inbox. 
IsRecvToken(l) ==
    \* Log statement was printed by the receiver.
    /\ l.event = "<"
    /\ LET msg == l.pkt.msg 
           rcv == l.pkt.rcv IN
        \* Log statement is about a token message.
        /\ msg.type = "tok"
        \* The number of payload messages in the node's inbox do not change.
        /\ \A n \in Node:
                SelectSeq(inbox[n], PayloadPred) = SelectSeq(inbox'[n], PayloadPred)
        \* The receivers's inbox contains a tok message in the next state.
        /\ \E idx \in DOMAIN inbox'[rcv]:
            /\ inbox'[rcv][idx].type = "tok"
            /\ inbox'[rcv][idx].q = msg.q
            /\ inbox'[rcv][idx].color = msg.color
        /\ UNCHANGED <<active, counter, color>>

IsSendMsg(l) ==
    \* Log statement was printed by the sender.
    /\ l.event = ">"
    \* Log statement is about a payload message. 
    /\ l.pkt.msg.type = "pl"
    /\ <<SendMsg(l.pkt.snd)>>_vars
    /\ LET rcv == l.pkt.rcv IN
        \* The sender's inbox remains unchanged, but the receivers's inbox contains one more
         \* pl message.  In the implementation, the message is obviously in flight, i.e. it 
         \* is send via the wire to the receiver.  However, the  SendMsg  action models it
         \* such that the message is atomically appended to the receiver's inbox. 
        Len(SelectSeq(inbox[rcv], PayloadPred)) < Len(SelectSeq(inbox'[rcv], PayloadPred))

IsRecvMsg(l) ==
    \* Log statement was printed by the receiver.
    /\ l.event = "<"
    /\ l.pkt.msg .type = "pl"
    /\ <<RecvMsg(l.pkt.rcv)>>_vars

IsDeactivate(l) ==
    \* Log statement was printed by the receiver.
    /\ l.event = "d"
    /\ <<Deactivate(l.node)>>_vars

IsTrm(l) ==
    \* "trm" messages are not part of EWD998, and, thus, not modeled in EWD998Chan.  We map
     \* "trm" messages to (finite) stuttering, essentially, skipping the "trm" messages in
     \* the log.  One could have also preprocessed/filtered the trace log, but the extra
     \* step is not necessary.
    /\ l.event \in {"<", ">"}
    /\ l.pkt.msg.type = "trm"
    \* The (mere) existance of a "trm" message implies that *all* nodes have terminated.
    /\ \A n \in Node: ~active[n]
    \* Careful! Without UNCHANGED vars, isTrm is true of all states of the high-level spec
     \* if the current line is a trm message.  In general, it is good practice to constrain
     \* all spec variables!
    /\ UNCHANGED vars

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
              /\ \/ IsInitiateToken(logline)
                 \/ IsPassToken(logline)
                 \/ IsRecvToken(logline)
                 \/ IsSendMsg(logline)
                 \/ IsRecvMsg(logline)
                 \/ IsDeactivate(logline)
                 \/ IsTrm(logline)
              \* Fail trace validation if the log contains a failure message. As an alternative,
               \* we could have used  TraceInv below, which would cause TLC to print the current
               \* trace upon its violation.  For the sake of consistency, we use the 
               \*  TraceAccepted  approach for all trace validation.
              /\ "failure" \notin DOMAIN logline

TraceInv ==
    LET l == TraceLog[TLCGet("level")] IN
    /\ "failure" \notin DOMAIN l
    /\ (l.event \in {"<", ">"} /\ l.pkt.msg.type = "trm") => \A n \in Node: ~active[n]

-----------------------------------------------------------------------------

TraceView ==
    \* A high-level state  s  can appear multiple times in a system trace.  Including the
     \* current level in TLC's view ensures that TLC will not stop model checking when  s
     \* appears the second time in the trace.  Put differently,  TraceView  causes TLC to
     \* consider  s_i  and s_j  , where  i  and  j  are the positions of  s  in the trace,
     \* to be different states.
    <<vars, TLCGet("level")>>

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


TODOs
-----

A)
 Check how useful spec coverage of EWD998Chan is to determine if we've
 seen enough traces => This would suggest to make it possible to check
 a set of traces instead of single traces one by one, or make it possible
 to merge multiple coverage statistics originating from multiple TLC runs
 (IIRC Jesse requested this one => find Github issue^1).  Fundamentally, a set
 of traces isn't hard; just add another variable or TLCGet("...") cleverness
 to the spec that equals the particular trace "id".  However, the json log is 
 current not set up for this because we wouldn't know where one trace in
 the log file starts and ends, unless we parse the whole log.  For this,
 non newline-delim json is probably the better choice.
 
 ^1 TLC should expose coverage statistics via, e.g., TLCGet("stats"). Users
 can then "dump" its output in a TLC post condition.  Afterward, multiple
 dumps can be combined either in TLA+ with e.g. a bit of repl'ing or in
 json.

B)
 TLC prints the last log line when the trace cannot be mapped to any
 behavior in the spec's set of behaviors.  This is good enough for now,
 especially when combined with the TLA+ debugger.  However, users might
 prefer to see the prefix of the behavior that was mapped, up to the point
 where it failed.  For long traces, this might be prohibitively expensive,
 though, in which case we could show a suffix of the prefix.

C)
 TLC could provide a new mode that would allow to check a set of traces.  Such
 a mode could eliminate the need for the  TraceAccepted  ,  TraceView  formulas,
 and allow the removal of a few subformulas elsewhere.  However, a new mode 
 won't signicantly simplify a trace spec, but TLC could report a proper error
 trace for the longest trace prefix it accepted.  A simpler "hack" would be
 to somehow expose the last state, and, thus, trace in the post condition. Also,
 the mode could warn users if  TraceNextConstraint  does not constrain all variables.