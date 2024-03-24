---------------------------- MODULE EWD687a_anim ---------------------------
EXTENDS EWD687a, Integers, Sequences, SVG, TLC, IOUtils

Repeat(str, n) ==
    (* Concatenates the given string str n times. The empty string is *)
    (* returned if n is less than 1. *)
    (* "m", 0 -> ""  *)
    (* "m", 1 -> "m"  *)
    (* "m", 2 -> "mm"  *)
    (* "m", 3 -> "mmm"  *)
    (* ... *)
    LET R[ i \in 0..n ] ==
        IF i = 0 THEN ""
        ELSE R[i-1] \o str
    IN R[n]

----------------------------------------------------------------------------

SVGDefs ==
    (* Defines an arrow with plain SVG that is referenced in the def of E below. *)
    \* Increasing refX moves the arrowhead to the middle of the line away from the tip.
    "<defs><marker id='arrow' markerWidth='35' markerHeight='35' refX='14' refY='3' orient='auto' markerUnits='strokeWidth' viewBox='0 0 20 20'><path d='M0,0 L0,6 L9,3 z' fill='black' /></marker></defs>"

----------------------------------------------------------------------------

Legend ==
    (* 
       Legend with four rows of labels (text) whose top-left point is located at BasePos:
       1: The current state ordinal.
       2: The action from the predecessor state to the current state.
       3: The action from the current state to the next/successor state.
       4: "~neutral procs red, round when also active".
    *)
    LET BasePos == [ x |-> 350, y |-> 120 ]
        (* The name of the action concatenated with the action's context. *)
        Action == TLCGet("action").name \o ToString(TLCGet("action").context) IN
    Group(<<Text(BasePos.x, BasePos.y, "Step: " \o ToString(TLCGet("level")), <<>>),
            Text(BasePos.x, BasePos.y + 20, "A:  " \o Action, <<>>),
            Text(BasePos.x, BasePos.y + 40, "A': " \o Action', <<>>),
            Text(BasePos.x, BasePos.y + 60, "~neutral procs red, round when also active", <<>>)>>,
            <<>>)

----------------------------------------------------------------------------

NodeDimension ==
    32

ArrowPosOffset ==
    \* NodeDimension ought to be divisible by 2 for proper alignment of nodes and edges.
    NodeDimension \div 2

GraphNodePos ==
    (* A function from processes to x,y coordinates: [ Procs -> [x: Nat, y: Nat] *)
    (* The coordinates are chosen according to the given layout algorithm parameterized *)
    (* by the given "options" record. *)
    NodesOfDirectedMultiGraph(Procs, Edges, 
        [algo |-> "Sugiyama",
         view_width |-> 1000, view_height |-> 1800, layering |-> "LONGEST_PATH",
         node_width |-> NodeDimension * 3, node_height |-> NodeDimension * 3])

----------------------------------------------------------------------------

N ==
    (* An SVG group containing rectangles denoting the graph of processes. Approximately at *)
    (* the center of each node, a text indicates the processes name (Procs). *)
    (* A black square denotes an idle process, a red circle an active one. *)
    LET NS[ p \in Procs ] ==         
        LET coord == GraphNodePos[p]    
            id == Text(coord.x + ArrowPosOffset - 5, coord.y + ArrowPosOffset + 7,
                        ToString(p), [fill |-> "white"])
            node == Rect(coord.x, coord.y, NodeDimension, NodeDimension,
                        \* round (rx=15) if node is active.
                        [ rx |-> IF active[p] THEN "15" ELSE "0",
                          fill |-> IF ~neutral(p) THEN "red" ELSE "black" ])
        IN Group(<<node, id>>, <<>>)
    IN Group(NS, <<>>)

E == 
    (* An SVG group containing lines denoting the (graph) edges. An line, *)
    (* connecting a from and to node, is annotated with three labels: *)
    LET ES[ e \in Edges ] ==
        LET from == GraphNodePos[e[1]] to == GraphNodePos[e[2]]
            (* 1: At the mid-point of the line, a string indicates the in-flight messages and ACKs, *)
            (*    or the empty string if there are no messages in flight. An in-flight message is   *)
            (*    denoted by an "m" and an ACK by an "a", respectively. *)
            mpt == PointOnLine(from, to, 2)
            messages == Text(mpt.x, mpt.y, 
                Repeat("m", msgs[e]) \o Repeat("a", acks[e]), <<>>)
            (* 2: At the quad-point towards the source of the edge, a negative integer denotes the  *)
            (*    number of unacknowledged messages. If there are zero unacknowledged messages, the *)
            (*    integer made invisible to reduce visual clutter. *)
            fpt == PointOnLine(from, to, 4)
            sent == Text(fpt.x, fpt.y, 
                IF sentUnacked[e] > 0 THEN ToString(-1 * sentUnacked[e]) ELSE "", 
                <<>>) 
            (* 3: At the quad-point towards the sink of the edge, a natural denotes the number of *)
            (*    ACKs that the sink still has to sent. Again, if there are zero ACKs to be sent  *)
            (*    the natural is invisible. *)
            tpt == PointOnLine(to, from, 4)
            rcvd == Text(tpt.x, tpt.y, 
                IF rcvdUnacked[e] > 0 THEN ToString(rcvdUnacked[e]) ELSE "", 
                <<>>) 
            line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset, 
                            to.x + ArrowPosOffset, to.y + ArrowPosOffset,
                            \* A solid, black line with an arrow at its tip denotes an edge.
                            [ stroke |-> "black", stroke_width |-> "2",
                              marker_end |-> "url(#arrow)" ])
        IN Group(<<line, messages, sent, rcvd>>, <<>>)
    IN Group(ES, <<>>)

U == 
    (* An SVG group containing the lines visualizing the upEdges of the overlay tree. *)
    LET UE[ u \in {upEdge[p] : p \in DOMAIN upEdge} \ {NotAnEdge} ] ==
        LET from == GraphNodePos[u[1]] to == GraphNodePos[u[2]]
            line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset, 
                        to.x + ArrowPosOffset, to.y + ArrowPosOffset,
                        (* An upEdge is denoted by a dashed, orange line. *)
                        [stroke |-> "orange", stroke_dasharray |-> "5", stroke_width |-> "5"])
        IN Group(<<line>>, <<>>)
    IN Group(UE, <<>>)

Frame ==
    (* Combine the (SVG) definitions, legend, processes, edges, and upEdges into a single *) 
    (* (SVG) frame as a visualization of the current TLA+ state. *)
    SVGDefs \o SVGElemToString(Group(<<Legend, E, U, N>>, <<>>))

----------------------------------------------------------------------------

ToFile(str, prefix, n, padding, suffix) ==
    (* Writes the given string str to a file whose name contains the number n. *)
    IOExecTemplate(
        \* %%03d to escape %03d in Java format strings.
        <<"bash", "-c", "echo \"%1$s\" > %2$s$(printf %%0%4$sd %3$s)%5$s">>,
            <<str, prefix, ToString(n), ToString(padding), suffix>>)

Alias == [
    \* active |-> active,
    \* sentUnacked |-> sentUnacked,
    \* rcvdUnacked |-> rcvdUnacked,
    \* msgs |-> msgs,
    \* acks |-> acks

    (* https://animator.tlapl.us (interactively explore the animation) *)
    _animator |-> 
        Frame
        ,
    (* The resulting set of EWD687a_anim_???.svg files can be rendered as an animated gif with:    *)
    (*   $ convert -delay 100 -density 200 *.svg EWD687a.gif *)
    (* An animated gif is portable across browser, but cannot be advanced/reversed manually,       *)
    (* unless a user installs a browser plugin such as https://github.com/0ui/gif-scrubber.        *)
    file |-> 
        \* The animator nests frame in an SVG box.  With a file, this is done explicitly.
        ToFile("<svg viewBox='0 0 1400 1200'>" \o Frame \o "</svg>", "EWD687a_anim_", TLCGet("level"), 3, ".svg")
    ]

----------------------------------------------------------------------------

InterestingBehavior ==
    \* A counter-example that is a violation of this property is a prefix of a behavior of at least
    \* 30 states with the Leader neutral in the final state.
    TLCGet("level") > 20 => ~neutral(Leader)

NoSuperfluousIdleSteps ==
    \* Disable Idle steps that leave the variables unchange (an idle process becoming idle)
    \* to prevent finite stuttering when simulating.
    ~UNCHANGED vars

----------------------------------------------------------------------------

\* Processes.
CONSTANTS L, P1, P2, P3, P4, P5

\* A randomly generate network of processes.
\* NodesOfNetwork ==
\*     {L, P1, P2, P3, P4, P5}

\* Network ==
\*     LET Edgs == SUBSET { n \in (NodesOfNetwork \X NodesOfNetwork):
\*                     \* No self-loops.
\*                     /\ n[1] # n[2]
\*                     \* L is a source and never a sink.
\*                     /\ n[2] # L }
\*     IN TLCEval(RandomElement(Edgs))

\* \* Print the randomly chosen set of edges.
\* ASSUME PrintT(<<"Edges", Edges>>)

\* A specific network of processes. 
Network ==
    { <<L, P1>>, <<L, P2>>, <<L, P3>>, 
        <<P1, P2>>, <<P1, P4>>,
        <<P2, P3>>, <<P2, P5>>, 
        <<P4, P3>>, <<P4, P5>>, 
        <<P3, P1>>, <<P3, P5>>,
        <<P5, P4>>}

NodesOfNetwork ==
    { e[1] : e \in Network } \cup { e[2] : e \in Network }

----------------------------------------------------------------------------
=============================================================================
\* Modification History
\* Last modified Tue Dec 21 17:52:54 PST 2021 by Markus Kuppe
\* Created Tue Dec 02 17:23:43 PDT 2021 by Markus Kuppe
