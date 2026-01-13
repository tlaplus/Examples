--------------------------- MODULE SlidingPuzzles_anim ---------------------------
EXTENDS TLC, SVG, SequencesExt, SlidingPuzzles

\* Layout constants
CELL_SIZE == 60
CELL_SPACING == 2
BASE_X == 30
BASE_Y == 50
BOARD_WIDTH == W * (CELL_SIZE + CELL_SPACING)
BOARD_HEIGHT == H * (CELL_SIZE + CELL_SPACING)

\* Map piece directly to color based on size and orientation
PieceColor(piece) ==
    LET size == Cardinality(piece)
        \* For 2-cell pieces: vertical means same x-coordinate, horizontal means same y-coordinate
        isVertical == size = 2 /\ \A p1, p2 \in piece : p1[1] = p2[1]
    IN CASE size = 0 -> "#ecf0f1"      \* Empty cells
         [] size = 1 -> "#95a5a6"      \* Gray - single pieces
         [] size = 2 /\ isVertical  -> "#3498db"  \* Blue - vertical 2x1
         [] size = 2 /\ ~isVertical -> "#1abc9c"  \* Teal - horizontal 1x2
         [] size = 4 -> "#e74c3c"      \* Red - 2x2 goal piece
         [] OTHER -> "#cccccc"         \* Fallback

\* Goal position (the 2x2 piece should reach bottom center)
GoalPositions == {<<1, 3>>, <<1, 4>>, <<2, 3>>, <<2, 4>>}

\* Find which piece occupies a given position
PieceAt(pos) ==
    IF \E piece \in board : pos \in piece
    THEN CHOOSE piece \in board : pos \in piece
    ELSE {}  \* Empty

\* Draw a single cell
CellRect(x, y, w, h, piece) ==
    LET fillColor == PieceColor(piece)
        strokeColor == "#2c3e50"
        strokeWidth == IF piece = {} THEN "1" ELSE "2"
    IN Rect(x, y, w, h, 
           ("fill" :> fillColor @@ 
            "stroke" :> strokeColor @@ 
            "stroke-width" :> strokeWidth @@ 
            "rx" :> "3"))

\* Draw the grid showing all positions
GridCells ==
    LET cellElems == {
            LET pos == <<x, y>>
                piece == PieceAt(pos)
                cellX == BASE_X + x * (CELL_SIZE + CELL_SPACING)
                cellY == BASE_Y + y * (CELL_SIZE + CELL_SPACING)
            IN CellRect(cellX, cellY, CELL_SIZE, CELL_SIZE, piece)
            : x \in 0..W-1, y \in 0..H-1
        }
    IN Group(SetToSeq(cellElems), <<>>)

\* Draw goal position indicator (subtle border around goal area)
GoalIndicator ==
    LET minX == BASE_X + 1 * (CELL_SIZE + CELL_SPACING) - 4
        minY == BASE_Y + 3 * (CELL_SIZE + CELL_SPACING) - 4
        width == 2 * (CELL_SIZE + CELL_SPACING) + 4
        height == 2 * (CELL_SIZE + CELL_SPACING) + 4
    IN Rect(minX, minY, width, height,
           ("fill" :> "none" @@ 
            "stroke" :> "#f1c40f" @@ 
            "stroke-width" :> "3" @@ 
            "stroke-dasharray" :> "5,5" @@
            "rx" :> "5"))

\* Title
Title == 
    Text(BASE_X + BOARD_WIDTH \div 2, BASE_Y - 25, "Klotski Puzzle", 
         ("text-anchor" :> "middle" @@ 
          "font-size" :> "20px" @@ 
          "font-weight" :> "bold" @@ 
          "fill" :> "#2c3e50"))

\* Subtitle explaining goal
Subtitle == 
    Text(BASE_X + BOARD_WIDTH \div 2, BASE_Y - 8, 
         "Move red piece to dashed area", 
         ("text-anchor" :> "middle" @@ 
          "font-size" :> "11px" @@ 
          "fill" :> "#7f8c8d"))

\* Step counter - positioned below the board to avoid overlap
StepCounter == 
    Text(BASE_X + BOARD_WIDTH \div 2, BASE_Y + BOARD_HEIGHT + 20, 
         "Step " \o ToString(TLCGet("level")), 
         ("text-anchor" :> "middle" @@ 
          "font-size" :> "12px" @@ 
          "font-family" :> "monospace" @@ 
          "fill" :> "#95a5a6"))

\* Success indicator (shows when puzzle is solved)
SuccessIndicator ==
    LET solved == ~KlotskiGoal  \* Puzzle is solved when KlotskiGoal invariant is violated
        checkX == BASE_X + BOARD_WIDTH + 30
        checkY == BASE_Y + 20
    IN Group(<<
        SVGElem("circle",
               ("cx" :> ToString(checkX) @@ 
                "cy" :> ToString(checkY) @@ 
                "r" :> "15" @@ 
                "fill" :> "#2ecc71" @@ 
                "stroke" :> "#27ae60" @@ 
                "stroke-width" :> "2"),
               <<>>,
               ""),
        SVGElem("path",
               ("d" :> "M " \o ToString(checkX - 6) \o " " \o ToString(checkY) \o 
                       " L " \o ToString(checkX - 2) \o " " \o ToString(checkY + 5) \o 
                       " L " \o ToString(checkX + 7) \o " " \o ToString(checkY - 5) @@
                "stroke" :> "white" @@
                "stroke-width" :> "3" @@
                "fill" :> "none" @@
                "stroke-linecap" :> "round" @@
                "stroke-linejoin" :> "round"),
               <<>>,
               "")
    >>, IF solved THEN <<>> ELSE ("opacity" :> "0"))

\* Main animation view combining all elements
AnimView == 
    Group(<<Title, Subtitle, GoalIndicator, GridCells, 
            StepCounter, SuccessIndicator>>, <<>>)

\* Wrap view in SVG document
AnimDoc == SVGDoc(AnimView, 0, 0, 
                  BASE_X + BOARD_WIDTH + 60, 
                  BASE_Y + BOARD_HEIGHT + 40, 
                  <<>>)

\* For TLC model checking (generates numbered frames for screencasts)
AnimAlias ==
    [board |-> board] @@
    [_anim |-> SVGSerialize(AnimDoc, "SlidingPuzzles_anim_", TLCGet("level"))]

\* For interactive debugging (live preview in debugger)
AnimWatch ==
    SVGSerialize(AnimDoc, "SlidingPuzzles_anim", 0)

=============================================================================
