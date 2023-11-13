------------------------------- CONFIG EWD998_anim -------------------------------
CONSTANTS
    Node = {"a", "b", "c", "d", "e", "f"} 
    RingOfNodes <- SomeRingOfNodes

SPECIFICATION 
    Spec

ALIAS
    Alias

\* HowTo Graphical Debugging (https://youtu.be/IO9ik850i0M):
\* - Uncomment ACTION_CONSTRAINT  ToSVG  and comment INVARIANT  AnimInv  instead
\* - Remove prime from  plsN  in  Messages (no double-priming allowed in TLA+)
\* - Remove ", Solid: Arrival in next" from  Labels (makes no sense in this mode)
\* - Run TLC with "-config EWD998_anim.tla EWD998_anim -simulate -note -debugger"
\* - Attach the VSCode debugger to the running TLC process
\* ACTION_CONSTRAINT
\*     ToSVG

INVARIANT 
    AnimInv
==================================================================================

------------------------------- MODULE EWD998_anim -------------------------------
EXTENDS EWD998ChanID, SVG, TLC, IOUtils

SomeRingOfNodes ==
    SimpleCycle(Node)

token == EWD998Chan!token
tpos == EWD998Chan!tpos


---------------------------------------------------------------------------

Arial == [font |-> "Arial"]

LegendBasePos == [ x |-> -5, y |-> 25 ]

RingBasePos == [w |-> 55, h |-> 55, r |-> 75]

\* 12pts (x/y) offset to be concentric with RingNetwork.
TokenBasePos == [ w |-> RingBasePos.w + 12, 
                  h |-> RingBasePos.h + 12,
                  r |-> RingBasePos.r + 25 ]

---------------------------------------------------------------------------
\* Labels

Labels == Group(<<Text(LegendBasePos.x, LegendBasePos.y, "Circle: Active, Black: Tainted", Arial),
                  Text(LegendBasePos.x, LegendBasePos.y + 20, "Line: Message, Arrow: Receiver", Arial),
                  Text(LegendBasePos.x, LegendBasePos.y + 40, "Dashed: In-Flight, Solid: Arrival in next", Arial),
                  Text(LegendBasePos.x, LegendBasePos.y + 60, "Level: " \o ToString(TLCGet("level")) \o 
                               " Terminated: " \o (IF EWD998Chan!EWD998!Termination THEN "T" ELSE "F") \o
                               " Detected: " \o (IF EWD998Chan!EWD998!terminationDetected THEN "T" ELSE "F"), Arial)>>,
                  <<>>)

---------------------------------------------------------------------------
NodeDimension == 26

\* Centers the line/circle at the center of a node instead of
\* a node's left upper corner (which are its 0:0 coordinates).
ArrowPosOffset == NodeDimension \div 2

\* Ring Network
RingNetwork ==
    LET RN[ n \in Node ] ==         
            LET coord == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, node2nat[n], N)    
                id == Text(coord.x + ArrowPosOffset + 2, coord.y + ArrowPosOffset + 7, ToString(counter[n]), 
                                                Arial @@ [fill |-> CHOOSE c \in Color : c # color[n]])
                node == Rect(coord.x, coord.y, NodeDimension, NodeDimension,
                                            \* round (rx=15) if node is active.
                                            [rx |-> IF ~active[n] THEN "0" ELSE "15",
                                            stroke |-> "black",
                                            fill |-> color[n]])
            IN Group(<<node, id>>, ("transform" :> "translate(0 125)"))
    IN Group(RN, <<>>)

---------------------------------------------------------------------------
\* Token ring (with larger radius than ring above and only visible at the node that currently holds the token).
TokenNetwork ==     
    LET coord == NodeOfRingNetwork(TokenBasePos.w, TokenBasePos.h, TokenBasePos.r, tpos, N)    
        circ  == Circle(coord.x-2, coord.y, 8, [stroke |-> "black", fill |-> token.color])
        id    == Text(coord.x - 5, coord.y + 3, ToString(token.q), [font |-> "Arial", fill |-> CHOOSE c \in Color : c # token.color ])
    \* Group always expects a sequence!
    IN Group(<<circ, id>>, ("transform" :> "translate(0 125)"))

---------------------------------------------------------------------------
\* Messages send from one node to another.  A proper arrow would be more intuitive with regards to the direction
\* of message flow but SVG doesn't natively has arrows.  This is why we use a lollipop instead where the ball
\* replaces the arrowhead. 

Messages ==
    LET M[ n \in Node ] ==
        LET pls == Range(SelectSeq(inbox[n], LAMBDA msg: msg.type = "pl"))
            plsN == Range(SelectSeq(inbox'[n], LAMBDA msg: msg.type = "pl"))
            I[ pl \in pls ] ==
                LET from == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, node2nat[pl.src], N)
                    to   == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, node2nat[n], N)
                    line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset, 
                                    to.x + ArrowPosOffset, to.y + ArrowPosOffset, 
                                    [stroke |-> "orange", stroke_dasharray |-> IF pl \in plsN THEN "5" ELSE "0",
                                     marker_end |-> "url(#arrow)"]) \* See Defs below for the definition of arrow.
                IN Group(<<line>>, ("transform" :> "translate(0 125)"))
        IN Group(I, <<>>)
    IN Group(M, <<>>)

---------------------------------------------------------------------------
Animation == SVGElemToString(Group(<<Labels, RingNetwork, TokenNetwork, Messages>>, <<>>))

\* This is just the arrow head that's used by the Message definition above as an attribute.
Defs ==
    "<defs><marker id='arrow' markerWidth='15' markerHeight='15' refX='0' refY='3' orient='auto' markerUnits='strokeWidth' viewBox='0 0 20 20'><path d='M0,0 L0,6 L9,3 z' fill='orange' /></marker></defs>"

ToSVG ==
    IOExecTemplate(
            <<"bash", "-c", "echo \"%1$s\" > EWD998_anim.svg">>,
                <<"<svg viewBox='-40 15 330 290'>"
                    \o Defs
                    \o Animation'  \* Note the prime here!
                >>).exitValue = 0

Alias == [ 
    toolbox |-> Defs \o Animation,
    eyeofgnome |-> "<svg viewBox='-80 0 300 300'>" \o Defs \o Animation \o "</svg>",
    toSVG |-> 
        IOExecTemplate(
            \* %%03d to escape %03d in Java format strings.
            <<"bash", "-c", "echo \"%1$s\" > EWD998_anim_$(printf %%03d %2$s).svg">>,
                <<"<svg viewBox='-40 15 330 290'>"
                    \o Defs
                    \o Animation
                    \o "</svg>", ToString(TLCGet("level"))>>)
    ]

---------------------------------------------------------------------------

AnimSpec ==
    \* AnimSpec constraints the set of initial states to a set of states,
    \* s.t. all nodes are inactive but have sent or received a message.
    \* The sum of all counters is zero.  The token is at the Initiator.
    \* The next-state relation does not permit environment (sub-) actions.
    \* Replacing Spec with AnimSpec above, TLC can generate traces for large
    \* numbers of nodes.
    /\ active = [ n \in Node |-> FALSE ]
    /\ color = [ n \in Node |-> "black" ]
    /\ counter = [n \in Node |-> IF Cardinality(Node) % 2 = 0
                                 THEN IF node2nat[n] % 2 = 0 
                                      THEN 1
                                      ELSE -1
                                 ELSE IF n # Initiator 
                                      THEN IF node2nat[n] % 2 = 0
                                           THEN 1
                                           ELSE -1
                                      ELSE 0 ]
    /\ inbox = [n \in Node |-> IF n  = Initiator \* RingOfNodes[Initiator] 
                              THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
                              ELSE <<>>] \* with empty channels.
    /\ Init!5
    /\ [][\E n \in Node: System(n)]_vars

\* Property that leads to interesting traces when animated.

AnimInv == EWD998Chan!EWD998!terminationDetected => TLCGet("level") < 20 

=============================================================================

## Assuming the most recent Toolbox nightly build (https://nightly.tlapl.us/dist)
## installed to /opt/toolbox.  On macOS, install gawk with `brew install gawk` 
## (default nawk does not like the match).

/opt/toolbox/tla2tools.jar -simulate -noGenerateSpecTE -config EWD998_anim.tla EWD998_anim | gawk 'match($0,/<svg.*<\/svg>/) { n += 1; print substr($0,RSTART,RLENGTH) > sprintf("%03d", n) ".svg" }' && eog .


## The best viewer for a stack of SVGs is Gnome's Eye Of Gnome (eog) that
## is available for Win, macOS, and Linux.  In its preferences, one can replace
## the transparent background with a custom color. One can also run a slideshow
## with a custom frame rate.

----

## Unfortunately, the MacPorts package cannot be installed
## because of a broken dependency (https://trac.macports.org/ticket/61713).  Instead,
## one can use the browser-based TLA+ trace Animator at https://animator.tlapl.us.
## In this case, a slightly different awk matching is needed.  Optionally, pipe
## output of awk directly to xclip to send it to the clipboard ("| xclip").

/opt/toolbox/tla2tools.jar -simulate -noGenerateSpecTE -config EWD998_anim.tla EWD998_anim | gawk 'match($0,/toolbox = .*/) { print "[\ntb |->" substr($0, RSTART+9, RLENGTH) "\n]," }'
