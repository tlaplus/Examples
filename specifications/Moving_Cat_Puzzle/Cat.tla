You have N boxes numbered 1 to N, arranged on a line. A cat is hiding
in one of the boxes. Every night, she moves to an adjacent box, and
every morning, you have one chance to inspect a box to find her. How
do you find the cat?

Solution: You start at box 2 and move one by one to N - 1. Then you
observe N - 1 again and start moving back to box 2. Repeat and
eventually you will find the cat. E.g with 5 boxes you check 2, 3, 4,
4, 3, 2; with 4 boxes you check 2, 3, 3, 2.

There is a simpler solution if the number of boxes is odd. The
solution here works in both even and odd cases.

The puzzle is trivial / impossible for a single box, since the cat
cannot move.

---- MODULE Cat ----

EXTENDS Naturals

CONSTANTS
  Number_Of_Boxes

ASSUME Number_Of_Boxes >= 2

VARIABLES
  \* The box the cat is currently hiding in
  cat_box,

  \* The box that is observed
  observed_box,

  \* The direction in which our search is progressing
  direction

vars == <<cat_box, observed_box, direction>>

----------------------------------------------------------------------

Directions == {"left", "right"}

Boxes == 1 .. Number_Of_Boxes

Observed_Boxes == 2 .. Number_Of_Boxes - 1

----------------------------------------------------------------------

\* Initially the cat is in an arbitrary box. We start our search
\* anywhere in the pattern described by the solution.
Init ==
  /\ cat_box \in Boxes
  /\ observed_box \in Observed_Boxes
  /\ direction \in Directions

\* The action performed by the cat: she either moves left or
\* right. There is no wrap-around.
Move_Cat ==
  /\ \/ cat_box' = cat_box + 1
     \/ cat_box' = cat_box - 1
  /\ cat_box' \in Boxes

\* The action performed by us: we observe boxes one by one. If we hit
\* the end of our search we reverse direction. For N boxes, we
\* alternate between 2 and N - 1.
Observe_Box ==
  LET next_box == IF direction = "right"
                  THEN observed_box + 1
                  ELSE observed_box - 1
  IN \/ /\ next_box \in Observed_Boxes
        /\ observed_box' = next_box
        /\ UNCHANGED direction
     \/ /\ next_box \notin Observed_Boxes
        /\ direction' = CHOOSE d \in Directions: d /= direction
        /\ UNCHANGED observed_box

\* Each step both the cat moves, and we make a choice on where to
\* look. Note that while in the puzzle description these things happen
\* one after the other, in the spec here there is no need. We can do
\* both at the same time.
Next ==
  /\ Move_Cat
  /\ Observe_Box

Spec ==
  /\ Init
  /\ [][Next]_vars

  \* The cat must always make a move, it is not allowed to sit
  \* still. Note that we could also apply weak fairness directly to
  \* Next, but this seems more precise to me.
  /\ WF_cat_box(Move_Cat)

----------------------------------------------------------------------

\* The game ends if the cat is in the observed box. With the above
\* algorithm, this will eventually happen.
Victory == <>(observed_box = cat_box)

----------------------------------------------------------------------

TypeOK ==
  /\ cat_box \in Boxes
  /\ observed_box \in Observed_Boxes
  /\ direction \in Directions

====
