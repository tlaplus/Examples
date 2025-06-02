# The Prisoners & Switch Puzzle

A set of N prisoners, all in solitary cells, is offered a game. One of
them is randomly selected and placed in a special cell. This cell has
a lamp and prisoners can turn it off or on. Afterwards the prisoner is
returned back to their cell.

At any point a prisoner can announce to the warden that they have all
been in the cell at least once. If they are right everyone is
released. If they are wrong the game ends and they remain in prison
forever.

The prisoners are allowed to communicate and design a strategy before
the game starts. Afterwards they can no longer communicate.

The default version where the initial state of the light is off is
checked in [Prisoner.cfg](Prisoner.cfg).

There is a variant of the puzzle where the initial state of the light
in the cell is not known. This is checked in
[PrisonerLightUnknown.cfg](PrisonerLightUnknown.cfg).

## Note on the spec

The spec could be more compact by replacing the do nothing ELSE clause
in the actions with stutter steps, like so:

```TLA+
StandardAction(p) ==
  /\ p \in NormalPrisoner
  /\ light = "off"
  /\ signalled[p] < SignalLimit
  /\ light' = "on"
  /\ signalled' = [signalled EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<count, announced>>

CounterAction(p) ==
  /\ p = Designated_Counter
  /\ light = "on"
  /\ light' = "off"
  /\ count' = count + 1
  /\ announced' = (count' >= VictoryThreshold)
  /\ UNCHANGED <<signalled>>
```

In the end I decided against this as I wanted to model the individual
decision procedure of a prisoner as closely as possible.

I also did not want to remove the `p` from the `CounterAction` for a
similar reason - it's the counter's job to know what they are doing,
not the warden's.

## Note on the other prisoner puzzle

The light unknown variant is very similar to the other [prisoner
puzzle](../Prisoners) in this repository. I was not aware of this when
I created my version. This puzzle has a slightly different setup, but
at their core they are identical.

This puzzle has one light switch and prisoners are not forced to use
it.

The other puzzle has two switches, and prisoners are forced to use
exactly one. The puzzles are identical since you treat one switch as
the signal switch, and the other one is used if you want to "do
nothing".

One final difference is that this spec also works for a single
prisoner, which is of course trivial but still an interesting
corner-case. These are checked in [SoloPrisoner.cfg](SoloPrisoner.cfg)
and [SoloPrisonerLightUnknown.cfg](SoloPrisonerLightUnknown.cfg).
