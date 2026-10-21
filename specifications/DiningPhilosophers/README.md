# Dining Philosophers

This folder contains two independent specifications of the
[Dining Philosophers problem](https://en.wikipedia.org/wiki/Dining_philosophers_problem).

## From naive to correct (TLA+)

[`DiningPhilosophers.tla`](DiningPhilosophers.tla) models the forks directly.

The git history shows how the spec got there. The table lists, for each
commit, the properties for which TLC finds a counterexample:

| Step | Solution | Known as | Coordination | Deadlock | Livelock | Starvation | Spectacle |
|---|---|---|---|---|---|---|---|
| 1 | [Take the forks in any order](https://github.com/tlaplus/examples/commit/89da1aa3e41b33fdb00062fa0a0a57ef4494e211) | Unordered fork acquisition | none | yes | yes | yes | [open](https://will62794.github.io/spectacle/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Ftlaplus%2Fexamples%2F89da1aa3e41b33fdb00062fa0a0a57ef4494e211%2Fspecifications%2FDiningPhilosophers%2FDiningPhilosophers.tla&constants%5BN%5D=5) |
| 2 | Take the left fork before the right fork | [Naive (symmetric) solution](https://en.wikipedia.org/wiki/Dining_philosophers_problem#Problems) | none | yes | yes | yes |  |

This repository has specs of two other solutions:

- **Chandy-Misra:** philosophers hand clean forks to their neighbors on
  request. See [`DiningPhilosophersPCal.tla`](DiningPhilosophersPCal.tla)
  [below](#chandy-misra-pluscal).
- **Bakery:** hungry philosophers take a ticket, and the lowest ticket eats
  first. The ticket order gives a fair, first-come-first-served solution.
  Lamport's Bakery algorithm and its Boulangerie variant are in
  [`Bakery-Boulangerie`](../Bakery-Boulangerie). They solve mutual exclusion,
  not dining, but the ticket idea carries over.

[`DiningPhilosophers_anim.tla`](DiningPhilosophers_anim.tla) draws the table,
forks, and philosophers for any `N` and writes one SVG per state. The
animation comes from [Spectacle](https://github.com/will62794/spectacle).

![Animation of DiningPhilosophers](DiningPhilosophers_anim.gif)

## Chandy-Misra (PlusCal)

[`DiningPhilosophersPCal.tla`](DiningPhilosophersPCal.tla) is a PlusCal
algorithm of the
[Chandy-Misra solution](https://en.wikipedia.org/wiki/Dining_philosophers_problem#Chandy/Misra_solution).
Unlike in Dijkstra's formulation, philosophers here talk to each other: they
hand clean forks to their neighbors on request. It is based on the exercise
at [learntla.com](https://learntla.com/temporal-logic/operators/).
[`APDiningPhilosophersPCal.tla`](APDiningPhilosophersPCal.tla) adds the type
annotations that Apalache needs.
