------------------------------- MODULE EWD998_anim -------------------------------
(***************************************************************************
 * EWD998 Termination Detection Animation
 *
 * This animation file visualizes Dijkstra's EWD998 distributed termination 
 * detection algorithm. It shows a ring of nodes passing a token, where each 
 * node can be active/inactive and white/black (tainted). The animation 
 * displays:
 *   - Node states (active=circle, inactive=square; white/black coloring)
 *   - Message counters tracking sent/received messages
 *   - Token position and state (color + queue count)
 *   - Messages in flight between nodes
 *   - System status (RUNNING/TERMINATED/DETECTED)
 *
 * How Animation Works (Conceptual):
 *   Animation in TLA+ is an action-level formula. This means the animation
 *   operators have access to BOTH the current state (unprimed variables
 *   like `inbox`) AND the next state (primed variables like `inbox'`).
 *   The animation translates this state transition into an SVG frame that
 *   visualizes the system at that moment.
 *
 *   Key insight: Because we have both states, we can show:
 *     - What's happening NOW (current state values)
 *     - What's about to happen NEXT (by comparing current vs. next state)
 *
 * Architecture:
 *   - Extends EWD998ChanID (the base specification with channels)
 *   - Uses SVG module for visual elements and file serialization
 *   - Uses TLC for state inspection (TLCGet("level"))
 *
 * Best Practices Applied:
 *   - Deterministic ordering using SimpleCycle for consistent rendering
 *   - Consistent viewBox (760×420) across all frames
 *   - Step number displayed in bottom-right corner
 *   - Modular visual components (Legend, Status, Nodes, Token, Messages)
 *   - Clear visual language with legend explaining all symbols
 ***************************************************************************)
EXTENDS EWD998ChanID, SVG, TLC

\* Deterministic node ordering: ensures nodes appear in consistent positions
\* across all animation frames (Best Practice from Animation Guide)
SomeRingOfNodes == SimpleCycle(Node)

\* Aliased state variables from the EWD998Chan specification for convenience
token == EWD998Chan!token
tpos == EWD998Chan!tpos

---------------------------------------------------------------------------
\* VISUAL CONSTANTS AND POSITIONING
\*
\* This section defines the layout structure for the animation, including
\* font styles, positioning coordinates, and spacing. All positions are
\* calculated to fit within the 760×420 viewBox.
---------------------------------------------------------------------------

\* Font style definitions for consistent typography throughout the animation
Arial == [font |-> "Arial, sans-serif", font_size |-> "12"]
ArialSmall == [font |-> "Arial, sans-serif", font_size |-> "11", font_weight |-> "bold"]
ArialXSmall == [font |-> "Arial, sans-serif", font_size |-> "10", font_weight |-> "bold"]
ArialBold == [font |-> "Arial, sans-serif", font_size |-> "14", font_weight |-> "bold"]
ArialTitle == [font |-> "Arial, sans-serif", font_size |-> "18", font_weight |-> "bold"]

\* Top-left position for legend and title (20px from left, 30px from top)
LegendBasePos == [ x |-> 20, y |-> 30 ]

\* Ring network layout: centered horizontally in viewBox
\*   w: x-coordinate of ring center (380 = 760/2, horizontally centered)
\*   h: y-coordinate of ring center (55px from top)
\*   r: radius of the ring in pixels
RingBasePos == [w |-> 380, h |-> 55, r |-> 85]

\* Token path layout: concentric with node ring but with larger radius
\* The offset (15px in x/y, 30px additional radius) creates visual separation
\* so the token doesn't overlap with nodes. This makes the token path clearly
\* distinguishable from the node ring.
TokenBasePos == [ w |-> RingBasePos.w + 15, 
                  h |-> RingBasePos.h + 15,
                  r |-> RingBasePos.r + 30 ]

---------------------------------------------------------------------------
\* COLOR SCHEME
\*
\* Defines the visual language of the animation. Colors are chosen for:
\*   - Clarity: distinct colors for different states
\*   - Semantics: intuitive mapping (green=success, red=running, etc.)
\*   - Accessibility: sufficient contrast for readability
---------------------------------------------------------------------------

Colors == [
    nodeWhite |-> "#f8f9fa",        \* Light gray: untainted (white) node background
    nodeBlack |-> "#343a40",        \* Dark gray: tainted (black) node background
    tokenWhite |-> "#ffc107",       \* Amber/yellow: white token (no tainted nodes encountered)
    tokenBlack |-> "#6f42c1",       \* Purple: black token (encountered a tainted node)
    message |-> "#ff6b6b",          \* Bright red: message arriving now
    messageInFlight |-> "#ff9a9a",  \* Light red: message in-flight (arriving next state)
    statusRunning |-> "#dc3545",    \* Red: system is running
    statusTerminated |-> "#ffc107", \* Yellow/amber: system has terminated but not detected
    statusDetected |-> "#28a745",   \* Green: termination successfully detected
    text |-> "#212529",             \* Dark text for labels
    counter |-> "#0066cc"           \* Blue: message counter display
]

---------------------------------------------------------------------------
\* TITLE AND LEGEND
\*
\* The legend provides a visual key to help viewers understand the animation.
\* It explains the meaning of shapes, colors, and symbols used throughout.
\* This is a best practice for making animations self-documenting.
---------------------------------------------------------------------------

Title == 
    Text(LegendBasePos.x, LegendBasePos.y, 
         "EWD998 Termination Detection", 
         ArialTitle @@ [fill |-> Colors.text])

Legend == 
    Group(<<
        Title,
        \* Left column: Node state explanations
        Text(LegendBasePos.x, LegendBasePos.y + 25, 
             "● Round node = Active   ■ Square node = Inactive", 
             Arial @@ [fill |-> Colors.text]),
        Text(LegendBasePos.x, LegendBasePos.y + 42, 
             "White/Light = Untainted   Black/Dark = Tainted", 
             Arial @@ [fill |-> Colors.text]),
        Text(LegendBasePos.x, LegendBasePos.y + 59, 
             "Counter (C:n) tracks sent/received messages", 
             Arial @@ [fill |-> Colors.counter]),
        \* Right column: Token and message explanations
        Text(LegendBasePos.x + 350, LegendBasePos.y + 25, 
             "Token: ◯ = white   ● = black", 
             Arial @@ [fill |-> Colors.text]),
        Text(LegendBasePos.x + 350, LegendBasePos.y + 42, 
             "Lines = Messages   Dashed = In-flight", 
             Arial @@ [fill |-> Colors.text])
    >>, <<>>)

---------------------------------------------------------------------------
\* STATUS DISPLAY
\*
\* Shows the current state of the termination detection algorithm.
\* Three possible states are displayed with distinct colors:
\*   - RUNNING (red): System is active, nodes may still be processing
\*   - TERMINATED (yellow): All nodes are inactive, but not yet detected
\*   - TERM. DETECTED (green): Termination successfully detected by algorithm
\*
\* This provides immediate feedback about whether the algorithm has completed
\* its goal of detecting termination.
---------------------------------------------------------------------------

StatusInfo == 
    LET \* Query the underlying specification for termination state
        isTerminated == EWD998Chan!EWD998!Termination
        isDetected == EWD998Chan!EWD998!terminationDetected
        \* Determine status text based on current state
        statusText == IF isDetected THEN "TERM. DETECTED"
                      ELSE IF isTerminated THEN "TERMINATED" 
                      ELSE "RUNNING"
        \* Color-code the status for quick visual recognition
        statusColor == IF isDetected THEN Colors.statusDetected
                       ELSE IF isTerminated THEN Colors.statusTerminated
                       ELSE Colors.statusRunning
    IN Group(<<
        \* Status box: rounded rectangle background
        Rect(LegendBasePos.x + 550, LegendBasePos.y - 10, 160, 35,
            [fill |-> statusColor, 
             stroke |-> Colors.text,
             stroke_width |-> "2",
             rx |-> "8",                  \* Rounded corners
             opacity |-> "0.9"]),
        \* Status text: white text centered in the box
        Text(LegendBasePos.x + 630, LegendBasePos.y + 13, statusText,
            ArialBold @@ [fill |-> "#ffffff", text_anchor |-> "middle"])
    >>, <<>>)

---------------------------------------------------------------------------
\* STEP NUMBER DISPLAY
\*
\* Best Practice (from Animation Guide): Every animation frame MUST include
\* a step number to track progression through the state space. The step
\* number should appear in a consistent location across all frames, similar
\* to page numbers in documents.
\*
\* TLCGet("level") returns the current depth in the state graph exploration.
---------------------------------------------------------------------------

StepNumber == 
    Text(730, 405, "Step " \o ToString(TLCGet("level")), 
         ("text-anchor" :> "end" @@      \* Right-aligned
          "font-size" :> "12px" @@ 
          "font-family" :> "monospace" @@\* Monospace for consistent digit width
          "fill" :> "#666"))             \* Subtle gray color

---------------------------------------------------------------------------
\* NODE RENDERING
\*
\* Nodes are the core elements of the algorithm. Each node has multiple
\* visual properties that encode its state:
\*   - Shape: Circle if active, Square if inactive
\*   - Color: Light (white) if untainted, Dark (black) if tainted
\*   - Label: Node ID number centered in the shape
\*   - Counter: "C:n" display below showing message balance
\*
\* The node ring is positioned using NodeOfRingNetwork, which calculates
\* polar coordinates for evenly-spaced nodes around a circle.
\*
\* Compatibility Note: NodeOfRingNetwork is not implemented in Spectacle,
\* making this animation incompatible with Spectacle's animation viewer.
---------------------------------------------------------------------------

NodeDimension == 30  \* Width/height of square nodes
NodeRadius == 15     \* Radius of circular nodes (also half of NodeDimension)

\* ArrowPosOffset: Centers message line endpoints at node centers.
\* SVG Rect coordinates specify the top-left corner, but Circle coordinates
\* specify the center, so we add NodeRadius to align message arrows properly.
ArrowPosOffset == NodeRadius

\* Ring Network: Creates visual representation of all nodes in the ring
RingNetwork ==
    LET \* Function that creates a visual element for each node
        RN[ n \in Node ] ==         
            LET \* Calculate (x,y) position for this node on the ring
                coord == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, node2nat[n], N)    
                
                \* Map node color state to visual colors
                \* "white" nodes are untainted (have not sent messages while black)
                \* "black" nodes are tainted (have sent messages while black)
                nodeColor == IF color[n] = "white" 
                            THEN Colors.nodeWhite 
                            ELSE Colors.nodeBlack
                \* Text color contrasts with node color for readability
                textColor == IF color[n] = "white" 
                            THEN Colors.nodeBlack 
                            ELSE Colors.nodeWhite
                
                \* Node shape encodes activity status:
                \* Active nodes = Circle (nodes that can still send/receive messages)
                \* Inactive nodes = Square/Rectangle (idle nodes)
                node == IF active[n]
                       THEN Circle(coord.x + NodeRadius, coord.y + NodeRadius, NodeRadius,
                                  [fill |-> nodeColor,
                                   stroke |-> Colors.text,
                                   stroke_width |-> "2.5",
                                   opacity |-> "0.95"])
                       ELSE Rect(coord.x, coord.y, NodeDimension, NodeDimension,
                                [fill |-> nodeColor,
                                 stroke |-> Colors.text,
                                 stroke_width |-> "2.5",
                                 rx |-> "3",           \* Slightly rounded corners
                                 opacity |-> "0.95"])
                
                \* Node ID label: displays the node number inside the shape
                id == Text(coord.x + NodeRadius, coord.y + NodeRadius + 5, 
                          ToString(node2nat[n]), 
                          Arial @@ [fill |-> textColor, 
                                   text_anchor |-> "middle",
                                   font_weight |-> "bold"])
                
                \* Counter display: tracks message balance (sent minus received)
                \* Positive = sent more messages than received
                \* Zero = balanced, meaning no messages in transit from this node
                \* All counters must be zero for valid termination detection
                cnt == Text(coord.x + NodeRadius, coord.y + NodeDimension + 18, 
                           "C:" \o ToString(counter[n]), 
                           ArialSmall @@ [fill |-> Colors.counter,
                                         text_anchor |-> "middle"])
            IN Group(<<node, id, cnt>>, ("transform" :> "translate(0 180)"))  \* Vertical offset
    IN Group(RN, <<>>)

---------------------------------------------------------------------------
\* TOKEN VISUALIZATION
\*
\* The token is a key element of EWD998. It circulates around the ring to
\* detect termination. The token carries two pieces of information:
\*   1. color: "white" or "black" (tracks if any node was black when passed)
\*   2. q: queue count accumulator (sum of counters from nodes that passed it)
\*
\* Visual representation:
\*   - Position: Moves around a larger concentric circle (TokenBasePos)
\*   - Color: Amber/yellow for white, Purple for black
\*   - Content: Displays the queue count (q value) inside the circle
\*   - Label: "Token" text above the circle
\*
\* The token path radius is larger than the node ring to prevent overlap
\* and make the token's movement clearly visible.
---------------------------------------------------------------------------

TokenNetwork ==     
    LET \* Calculate token position on its dedicated ring (concentric, larger radius)
        coord == NodeOfRingNetwork(TokenBasePos.w, TokenBasePos.h, TokenBasePos.r, tpos, N)    
        
        \* Token color encoding:
        \* White token (yellow/amber) = has not encountered any black nodes
        \* Black token (purple) = has encountered at least one black node
        tokenColor == IF token.color = "white" 
                     THEN Colors.tokenWhite 
                     ELSE Colors.tokenBlack
        \* Text color for queue value inside token
        textColor == IF token.color = "white" 
                    THEN Colors.nodeBlack 
                    ELSE "#ffffff"
        
        \* Token circle: larger and more prominent than node circles
        circ == Circle(coord.x + 10, coord.y + 10, 12, 
                      [fill |-> tokenColor,
                       stroke |-> Colors.text,
                       stroke_width |-> "2.5",
                       opacity |-> "1.0"])
        
        \* Queue count display: shows accumulated counter sum (q value)
        \* As the token circulates, each node adds its counter to q
        \* When token completes a round with q=0 and color=white, termination is detected
        qVal == Text(coord.x + 10, coord.y + 15, ToString(token.q), 
                    ArialSmall @@ [fill |-> textColor,
                                   text_anchor |-> "middle"])
        
        \* "Token" label above the circle for identification
        label == Text(coord.x + 10, coord.y - 5, "Token", 
                     ArialXSmall @@ [fill |-> Colors.text,
                                     text_anchor |-> "middle"])
    IN Group(<<circ, qVal, label>>, ("transform" :> "translate(0 180)"))  \* Vertical offset

---------------------------------------------------------------------------
\* MESSAGE VISUALIZATION
\*
\* Messages represent work being transferred between nodes. The animation
\* distinguishes between two types of message states:
\*   1. Arriving messages (solid lines): Messages being delivered in current step
\*   2. In-flight messages (dashed lines): Messages still in transit
\*
\* This distinction helps viewers understand the asynchronous nature of the
\* algorithm. A message sent in one step doesn't arrive until a later step.
\*
\* Visual encoding:
\*   - Solid red line + dark arrow = message arriving now
\*   - Dashed light red line + light arrow = message in-flight (will arrive later)
\*   - Direction: arrow points from sender to receiver
\*   - Arrow markers match their line colors for visual consistency
\*
\* Implementation notes: 
\*   - We compare inbox and inbox' (primed) to determine which messages are 
\*     arriving vs. remaining in-flight
\*   - Two arrow markers (arrowSolid, arrowDashed) defined in DefsElement provide
\*     direction indicators that match the line style
---------------------------------------------------------------------------

Messages ==
    LET \* For each destination node, create message visualizations
        M[ n \in Node ] ==
        LET \* Extract payload messages ("pl" type) from this node's inbox
            pls == Range(SelectSeq(inbox[n], LAMBDA msg: msg.type = "pl"))
            \* Extract payload messages in the NEXT state (primed)
            plsN == Range(SelectSeq(inbox'[n], LAMBDA msg: msg.type = "pl"))
            \* For each message in the current inbox, create a visual line
            I[ pl \in pls ] ==
                LET \* Get coordinates of sender and receiver nodes
                    from == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, node2nat[pl.src], N)
                    to   == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, node2nat[n], N)
                    \* Check if message persists in next state (in-flight) or is being delivered
                    isInFlight == pl \in plsN
                    \* Color and style based on message state
                    msgColor == IF isInFlight THEN Colors.messageInFlight ELSE Colors.message
                    dashArray == IF isInFlight THEN "6,4" ELSE "0"  \* SVG dash pattern
                    \* Arrow marker selection: use lighter arrow for dashed lines
                    arrowMarker == IF isInFlight THEN "url(#arrowDashed)" ELSE "url(#arrowSolid)"
                    \* Message line with directional arrow (points from sender to receiver)
                    line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset, 
                                to.x + ArrowPosOffset, to.y + ArrowPosOffset, 
                                [stroke |-> msgColor, 
                                 stroke_width |-> "2.5",
                                 stroke_dasharray |-> dashArray,
                                 opacity |-> IF isInFlight THEN "0.6" ELSE "0.9",
                                 marker_end |-> arrowMarker]) \* Arrow shows message direction
                IN Group(<<line>>, ("transform" :> "translate(0 180)"))  \* Vertical offset
        IN Group(I, <<>>)
    IN Group(M, <<>>)


---------------------------------------------------------------------------
\* ANIMATION COMPOSITION
\*
\* This section assembles all visual components into the final animation frame.
\* Components are layered in a specific order (z-order) to ensure proper
\* visual hierarchy.
---------------------------------------------------------------------------

\* Background: White rectangle covering the entire viewBox
\* This ensures a clean, consistent background across all frames
Background == 
    Rect(-20, 0, 760, 420, 
        [fill |-> "#ffffff", stroke |-> "none"])

\* SVG Definitions Element: Creates SVG <defs> with reusable arrow markers
\* This must be included in the SVG document for message arrows to render.
\* Two arrow markers are defined, matching their respective line styles:
\*   - arrowSolid: Dark red arrow for arriving messages
\*   - arrowDashed: Light red arrow for in-flight messages
DefsElement == 
    SVGElem("defs", <<>>, <<
        \* Arrow marker for solid message lines (arriving now)
        SVGElem("marker", 
            ("id" :> "arrowSolid" @@ 
             "markerWidth" :> "6" @@       \* Compact size for subtle direction indication
             "markerHeight" :> "6" @@ 
             "refX" :> "5" @@              \* Reference point for line attachment
             "refY" :> "2" @@ 
             "orient" :> "auto" @@         \* Auto-rotate to match line angle
             "markerUnits" :> "strokeWidth" @@ 
             "viewBox" :> "0 0 10 10"), 
            <<SVGElem("path", ("d" :> "M0,0 L0,6 L9,3 z" @@ "fill" :> Colors.message), <<>>, "")>>, 
            ""),
        \* Arrow marker for dashed message lines (in-flight)
        SVGElem("marker", 
            ("id" :> "arrowDashed" @@ 
             "markerWidth" :> "6" @@       \* Compact size for subtle direction indication
             "markerHeight" :> "6" @@ 
             "refX" :> "5" @@              \* Reference point for line attachment
             "refY" :> "2" @@ 
             "orient" :> "auto" @@         \* Auto-rotate to match line angle
             "markerUnits" :> "strokeWidth" @@ 
             "viewBox" :> "0 0 10 10"), 
            <<SVGElem("path", ("d" :> "M0,0 L0,6 L9,3 z" @@ "fill" :> Colors.messageInFlight), <<>>, "")>>, 
            "")
    >>, "")

\* AnimView: Main visual composition operator
\*
\* Best Practice (from Animation Guide): Create a single operator that composes
\* all visual elements. This provides a clean entry point for the animation.
\*
\* Layer ordering (bottom to top):
\*   0. DefsElement - SVG definitions (arrow markers, must be first)
\*   1. Background - white canvas
\*   2. Legend - title and key (always visible, explains symbols)
\*   3. StatusInfo - current algorithm state (running/terminated/detected)
\*   4. RingNetwork - the nodes in their ring formation
\*   5. TokenNetwork - the token (overlays the ring)
\*   6. Messages - message lines with arrows (drawn on top)
\*   7. StepNumber - step counter (topmost, bottom-right corner)
\*
\* This ordering ensures proper visual hierarchy and prevents elements from
\* obscuring each other inappropriately.
AnimView == 
    Group(<<
        DefsElement,   \* Layer 0: SVG definitions (arrow markers)
        Background,    \* Layer 1: White background
        Legend,        \* Layer 2: Title and legend
        StatusInfo,    \* Layer 3: Status indicator box
        RingNetwork,   \* Layer 4: Node ring
        TokenNetwork,  \* Layer 5: Token (on top of ring)
        Messages,      \* Layer 6: Message arrows (most prominent)
        StepNumber     \* Layer 7: Step counter (always visible)
    >>, <<>>)

---------------------------------------------------------------------------
\* ANIMATION WATCH EXPRESSION (for TLA+ Debugger)
\*
\* AnimWatch is designed for use as a Watch expression in the TLA+ Debugger.
\* When used with a live SVG viewer (e.g., https://open-vsx.org/extension/jock/svg),
\* the animation dynamically updates as you step through the debugger.
\*
\* Usage in Debugger:
\*   When debugging EWD998ChanID.tla, use this watch expression:
\*
\*     LET A == INSTANCE EWD998_anim IN A!AnimWatch
\*
\*   (You must instantiate EWD998_anim in your watch expression, because
\*   EWD998ChanID does not extend or instantiate EWD998_anim.)
\*
\* Frame parameter = 0:
\*   - Each new frame REPLACES the previous SVG file on disk
\*   - The SVG viewer automatically refreshes to show the current state
\*   - Perfect for interactive debugging: see live updates as you step through
\*   - Only one SVG file exists at a time (e.g., "EWD998_anim_watch_00.svg")
---------------------------------------------------------------------------

AnimWatch ==
    \* SVGSerialize writes one SVG file that updates with each state transition
    SVGSerialize(
        SVGDoc(AnimView, -20, 0, 760, 420, <<>>),  \* Complete SVG document
        "EWD998_anim_watch_",                      \* Filename prefix
        0)                                         \* Frame 0 (overwrites each time)
    
---------------------------------------------------------------------------
\* ANIMATION ALIAS FOR TLC (for Screencast Generation)
\*
\* Best Practice (from Animation Guide): The AnimAlias operator is a TLC alias
\* that combines state variable inspection with animation generation. When you
\* add "ALIAS AnimAlias" to your .cfg file, TLC will automatically call this
\* operator at each state during exploration.
\*
\* Structure:
\*   - Returns a record with state variables (active, color, counter, etc.)
\*     merged with the special _anim field
\*   - The _anim field contains the SVGSerialize call for animation generation
\*   - This allows both visual animation AND state value inspection in TLC output
\*
\* How the animation works:
\*   1. AnimView is evaluated to create SVG elements based on current state
\*   2. SVGDoc wraps the elements in a complete SVG document structure
\*   3. SVGSerialize (from SVG module) writes the SVG to disk
\*   4. Files are named "EWD998_anim_<N>.svg" where N is the state level
\*
\* Frame parameter = TLCGet("level"):
\*   - Each state generates a UNIQUE SVG file on disk
\*   - Creates a complete sequence: EWD998_anim_0.svg, EWD998_anim_1.svg, etc.
\*   - Perfect for creating screencasts: combine frames into GIF, MOV, MP4, etc.
\*   - All frames are preserved for post-processing and review
\*
\* ViewBox: -20, 0, 760, 420
\*   - Starts slightly left (-20) to accommodate background padding
\*   - 760×420 dimensions fit all elements with appropriate margins
\*   - Consistent viewBox across all frames (required for animation playback)
---------------------------------------------------------------------------

AnimAlias ==
    \* Record merge: state variables for debugging + _anim field for visualization
    [active |-> active, color |-> color, counter |-> counter, 
     inbox |-> inbox, clock |-> clock, passes |-> passes] @@
    [_anim |-> SVGSerialize(
        SVGDoc(AnimView, -20, 0, 760, 420, <<>>),  \* Complete SVG document
        "EWD998_anim_",                            \* Filename prefix
        TLCGet("level"))]                          \* Unique frame number per state

=============================================================================
