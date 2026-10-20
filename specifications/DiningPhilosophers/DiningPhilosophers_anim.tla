---- MODULE DiningPhilosophers_anim ----
EXTENDS TLC, Integers, Sequences, SVG, DiningPhilosophers

(***************************************************************************)
(* Every seat is drawn once, in the frame of the philosopher at the top of *)
(* the table, and then rotated about the table's center.  Philosophers are *)
(* placed counter-clockwise so that, facing the table, LeftFork(p) is at   *)
(* p's left hand and RightFork(p) at p's right hand.                       *)
(***************************************************************************)

\* Table radius.  Plates lie 25 inside the edge and need about 65 between
\* neighbors, so the table grows with N.
R == IF 25 + 11 * N > 80 THEN 25 + 11 * N ELSE 80

\* The table's top edge is at y = 70, which all seat coordinates rely on.
Cx == R + 70
Cy == R + 70

\* Angles are in tenths of a degree, in 0..7200 to avoid negative numbers.
SeatAngle(p) == 3600 - (3600 * (p - 1)) \div N
ForkAngle(f) == SeatAngle(f) + 1800 \div N   \* Fork f lies between seats f and f-1.

Deg(t) == ToString(t \div 10) \o "." \o ToString(t % 10)

RotateAboutCenter(t) ==
    "rotate(" \o Deg(t) \o " " \o ToString(Cx) \o " " \o ToString(Cy) \o ")"

\* Undo the rotation of the enclosing seat so that labels stay upright.
Upright(t, x, y) ==
    "rotate(" \o Deg(7200 - t) \o " " \o ToString(x) \o " " \o ToString(y) \o ")"

Show(cond, elem) == IF cond THEN <<elem>> ELSE <<>>

Label(x, y, t, str, size, color) ==
    Text(x, y, str,
        ("text-anchor" :> "middle" @@ "font-family" :> "sans-serif" @@
         "font-size" :> ToString(size) @@ "fill" :> color @@
         "transform" :> Upright(t, x, y - size \div 3)))

ThinkingColor == "#9db4d0"
HungryColor   == "#f2a541"
EatingColor   == "#5cb85c"

StateColor(p) ==
    CASE IsEating(p)                      -> EatingColor
      [] Cardinality(philosophers[p]) = 1 -> HungryColor
      [] OTHER                            -> ThinkingColor

(***************************************************************************)
(* A fork centered at (x, y), rotated by a degrees.  Unrotated, its tines  *)
(* point up.                                                               *)
(***************************************************************************)
ForkGlyph(x, y, a) ==
    LET style(w) == ("stroke" :> "#5a5a5a" @@ "stroke-width" :> w @@
                     "stroke-linecap" :> "round")
    IN Group(<<
        Line(0, 2, 0, 14, style("3")),
        Line(-4, -2, 4, -2, style("1.5")),
        Line(-4, -2, -4, -13, style("1.5")),
        Line( 0, -2,  0, -13, style("1.5")),
        Line( 4, -2,  4, -13, style("1.5"))
       >>,
       ("transform" :> "translate(" \o ToString(x) \o " " \o ToString(y) \o
                       ") rotate(" \o ToString(a) \o ")"))

Table ==
    Circle(Cx, Cy, R, ("fill" :> "#deb887" @@ "stroke" :> "#a0764a" @@
                       "stroke-width" :> "3"))

\* A plate in front of philosopher p, with food on it while p eats.
Plate(p) ==
    Group(<<
        Circle(Cx, 95, 15, [fill |-> "white", stroke |-> "#999"]),
        Circle(Cx, 95, 10, [fill |-> "none", stroke |-> "#ddd"])
      >> \o
      Show(IsEating(p), Circle(Cx, 95, 7, [fill |-> "#e07b39"])),
      ("transform" :> RotateAboutCenter(SeatAngle(p))))

\* Philosopher p with an arm and a fork for each fork that p holds.
Philosopher(p) ==
    LET t     == SeatAngle(p)
        arm(x1, x2) == Line(x1, 52, x2, 62,
                            ("stroke" :> StateColor(p) @@ "stroke-width" :> "6" @@
                             "stroke-linecap" :> "round"))
        hand(x)     == Circle(x, 61, 4, [fill |-> "#f6d7b0", stroke |-> "#555"])
        left  == LeftFork(p) \in philosophers[p]
        \* For N = 1, both hands would show the same, only, fork.
        right == RightFork(p) \in philosophers[p] /\ RightFork(p) # LeftFork(p)
    IN Group(
        Show(left,  arm(Cx + 10, Cx + 25)) \o
        Show(right, arm(Cx - 10, Cx - 25)) \o
        <<
          Rect(Cx - 18, 44, 36, 24, [rx |-> "12", fill |-> StateColor(p), stroke |-> "#555"]),
          Circle(Cx, 32, 12, [fill |-> "#f6d7b0", stroke |-> "#555"]),
          Label(Cx, 36, t, ToString(p), 12, "#333")
        >> \o
        \* Held forks point towards the plate.
        Show(left,  ForkGlyph(Cx + 22, 70, 200)) \o
        Show(right, ForkGlyph(Cx - 22, 70, 160)) \o
        Show(left,  hand(Cx + 25)) \o
        Show(right, hand(Cx - 25)),
        ("transform" :> RotateAboutCenter(t)))

\* Fork f on the table; only its number remains while someone holds it.
TableFork(f) ==
    Group(
      Show(f \in forks, ForkGlyph(Cx, 92, 180)) \o
      <<Label(Cx, 123, ForkAngle(f), ToString(f), 9, "#7a5230")>>,
      ("transform" :> RotateAboutCenter(ForkAngle(f))))

Legend ==
    LET x == 2 * Cx + 15
        entry(i, color, str) ==
            Group(<<
                Rect(x, 20 + 22 * i, 14, 14, [rx |-> "4", fill |-> color, stroke |-> "#555"]),
                Text(x + 20, 32 + 22 * i, str,
                     ("font-family" :> "sans-serif" @@ "font-size" :> "11" @@ "fill" :> "#333"))
              >>, <<>>)
    IN Group(<<
        entry(0, ThinkingColor, "thinking"),
        entry(1, HungryColor,   "hungry (1 fork)"),
        entry(2, EatingColor,   "eating (2 forks)")
      >>, <<>>)

\* Scale the drawing, in hundredths, to 600 wide, which fits Spectacle's pane.
ViewWidth == 600
Scale == (100 * ViewWidth) \div (2 * Cx + 130)
ViewHeight == (2 * Cy * Scale) \div 100

ScaleStr ==
    ToString(Scale \div 100) \o "." \o
    (IF Scale % 100 < 10 THEN "0" ELSE "") \o ToString(Scale % 100)

AnimView ==
    Group(<<Table>> \o
          [p \in P |-> Plate(p)] \o
          [f \in P |-> TableFork(f)] \o
          [p \in P |-> Philosopher(p)] \o
          <<Legend>>,
          ("transform" :> "scale(" \o ScaleStr \o " " \o ScaleStr \o ")"))

\* Animation alias for generating SVG files with TLC.
AnimAlias ==
    [
        philosophers |-> philosophers, forks |-> forks
    ] @@
    [ _anim |-> SVGSerialize(SVGDoc(AnimView, 0, 0, ViewWidth, ViewHeight, <<>>), "DiningPhilosophers_anim_", TLCGet("level")) ]

====
