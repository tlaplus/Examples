# Dining Philosophers

This folder contains specifications of the
[Dining Philosophers problem](https://en.wikipedia.org/wiki/Dining_philosophers_problem).

## From naive to correct (TLA+)

The git history builds a TLA+ spec of the forks, one solution per
commit. The table lists, for each commit, the properties for which TLC
finds a counterexample:

| Step | Solution | Known as | Coordination | Deadlock | Livelock | Starvation | Spectacle |
|---|---|---|---|---|---|---|---|

This repository has specs of two other solutions:

- **Chandy-Misra:** philosophers hand clean forks to their neighbors on
  request. See [`DiningPhilosophersPCal.tla`](DiningPhilosophersPCal.tla)
  [below](#chandy-misra-pluscal).
- **Bakery:** hungry philosophers take a ticket, and the lowest ticket eats
  first. The ticket order gives a fair, first-come-first-served solution.
  Lamport's Bakery algorithm and its Boulangerie variant are in
  [`Bakery-Boulangerie`](../Bakery-Boulangerie). They solve mutual exclusion,
  not dining, but the ticket idea carries over.

## Chandy-Misra (PlusCal)

[`DiningPhilosophersPCal.tla`](DiningPhilosophersPCal.tla) is a PlusCal
algorithm of the
[Chandy-Misra solution](https://en.wikipedia.org/wiki/Dining_philosophers_problem#Chandy/Misra_solution).
Unlike in Dijkstra's formulation, philosophers here talk to each other: they
hand clean forks to their neighbors on request. It is based on the exercise
at [learntla.com](https://learntla.com/temporal-logic/operators/).
[`APDiningPhilosophersPCal.tla`](APDiningPhilosophersPCal.tla) adds the type
annotations that Apalache needs.
