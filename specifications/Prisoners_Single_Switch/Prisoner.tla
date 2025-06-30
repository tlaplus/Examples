The prisoner puzzle. A set of N prisoners, all in solitary cells, is
offered a game. One of them is randomly selected and placed in a
special cell. This cell has a lamp and prisoners can turn it off or
on. Afterwards the prisoner is returned back to their cell.

At any point a prisoner can announce to the warden that they have all
been in the cell at least once. If they are right everyone is
released. If they are wrong the game ends and they remain in prison
forever.

The prisoners are allowed to communicate and design a strategy before
the game starts. Afterwards they can no longer communicate.

There is a variant of the puzzle where the initial state of the light
in the cell is not known.

In either case the strategy is:

  * One prisoner is designated as the counter.

  * Other prisoners, when they enter the cell turn the light on if its
    off. They do this at most once (or twice in the variant).

  * If the designated counter sees the light, they turn it off and
    increment their count. Once they count to N (or 2N - 1 for the
    variant), they know that everyone (including themselves) must have
    entered the cell and can announce victory.

Note: This puzzle is a variant of other prisoner puzzle here that I
was not aware of when I wrote this model.
https://github.com/tlaplus/Examples/tree/master/specifications/Prisoners

The setup is different: here there is only one switch, and the initial
status of it might be known, and the prisoners are not required to do
anything if they enter the room.

The solution is the same however (except we don't have the busy-work
switch), and our models are very similar.

---- MODULE Prisoner ----

EXTENDS FiniteSets, Naturals

CONSTANTS
  \* The set of prisoners playing the game. Has to be at least one.
  Prisoner,

  \* Configuration if the initial state of the light is "off" or
  \* unknown. The puzzle is harder (takes more steps) if we don't know
  \* the initial state.
  Light_Unknown

ASSUME Light_Unknown \in BOOLEAN

VARIABLES
  \* The counter's current count
  count,

  \* If the announcement has been made
  announced,

  \* How often other prisoners have signalled
  signalled,

  \* Current status of the light
  light,

  \* The warden's view on who has actually been to the cell
  has_visited

vars == <<count, announced, signalled, light, has_visited>>

------------------------------------------------------------------------------

\* The strategy differs slightly if the initial state of the light is
\* known or not. If it's "off" then a simple count to N is
\* sufficient. If the state is unknown we count to 2N - 1, and each
\* prisoner will signal up to two times.

SignalLimit == IF Light_Unknown THEN 2 ELSE 1

VictoryThreshold ==
  IF Light_Unknown
  THEN Cardinality(Prisoner) * 2 - 1
  ELSE Cardinality(Prisoner)

------------------------------------------------------------------------------

\* We pick somebody at random to be the counter
DesignatedCounter == CHOOSE p \in Prisoner: TRUE

\* The other prisoners
NormalPrisoner == Prisoner \ {DesignatedCounter}

\* The only thing to note here is that the count starts at one. Since
\* only the counter will make an announcement if they are in the cell,
\* this 1 means they have already counted themselves. We could also
\* model this with a separate variable to note when the counter has
\* visited the cell for the very first time, but this is not
\* necessary.
Init ==
  /\ count = 1
  /\ announced = FALSE
  /\ signalled = [ p \in NormalPrisoner |-> 0 ]
  /\ \/ Light_Unknown /\ light \in { "off", "on" }
     \/ ~Light_Unknown /\ light = "off"
  /\ has_visited = {}

------------------------------------------------------------------------------

\* The action taken by the designated counter, if they are placed in
\* the cell
\*
\* Note: we could simplify this change the IF to just be a
\* precondition to the action, and while that would be a more elegant
\* spec, I think this better models the decision procedure of the
\* prisoner.
CounterAction(p) ==
  /\ p = DesignatedCounter
  /\ IF light = "on"
     THEN
       /\ light' = "off"
       /\ count' = count + 1
     ELSE
       UNCHANGED <<light, count>>
  /\ announced' = (count' >= VictoryThreshold)
  /\ UNCHANGED <<signalled>>

\* The action taken by the other prisoners, if they are placed in the
\* cell
\*
\* Same note on the IF applies here.
StandardAction(p) ==
  /\ p \in NormalPrisoner
  /\ IF light = "off" /\ signalled[p] < SignalLimit
     THEN
       /\ light' = "on"
       /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
     ELSE
       UNCHANGED <<light, signalled>>
  /\ UNCHANGED <<count, announced>>

\* The action performed by the warden: place a prisoner in the cell
\* and maintain our own view of who's been selected (so we can judge
\* if a victory announcement is correct)
WardenAction(p) ==
  \* Put one of the prisoners in the cell
  /\ \/ CounterAction(p)
     \/ StandardAction(p)

  \* Maintain the warden's view
  /\ has_visited' = has_visited \union {p}

Next == \E p \in Prisoner: WardenAction(p)

Spec ==
  /\ Init
  /\ [][Next]_vars

  \* Base assumption in the game: the warden eventually has to choose
  \* everyone in a way progress is possible
  /\ \A p \in Prisoner: WF_vars(WardenAction(p))

------------------------------------------------------------------------------

\* Goal of the game: eventually the prisoners will win
Terminating == <>announced

------------------------------------------------------------------------------

\* Type invariant. Note it's possible to over-count in the lights
\* unknown version, if the initial state of the light is "on". Hence
\* the slightly more relaxed upper bound on count.
TypeOK ==
  /\ count \in 1 .. VictoryThreshold + 1
  /\ announced \in BOOLEAN
  /\ signalled \in [ NormalPrisoner -> 0 .. 2 ]
  /\ light \in {"off", "on"}
  /\ has_visited \subseteq Prisoner

\* Invariant to make sure victory is never declared in error
VictoryOK == announced => (has_visited = Prisoner)

====
