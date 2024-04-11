---- MODULE DiningPhilosophers ----

(*
TLA+ / PlusCal implementation of the Dining Philosophers problem.
Based on the exercise given in https://learntla.com/temporal-logic/operators/

This is an implementation of the Chandy-Misra solution.
https://en.wikipedia.org/wiki/Dining_philosophers_problem#Chandy/Misra_solution

In Dijkstra's original formulation of the problem, philosophers may not speak
to each other and cannot hand forks to each other.

In the Chandy-Misra formulation, philosophers may hand forks directly to each
other.

I ran this with alygin's TLA+ extension for VSCode:
  https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus
"> TLA+: Parse module" updates the translated TLA+ to match the PlusCal
  'algorithm' above.
"> TLA+: Check model with TLC" checks the model's correctness.

You can also use TLA+ Toolbox. You may need to "create a model" and
use the UI to add the invariants and properties at the bottom of this file.
*)

EXTENDS Integers, TLC

CONSTANTS
    \* Number of philosophers
    NP

ASSUME
    /\ NP \in Nat \ {0}

(* --algorithm DiningPhilosophers

variables
    forks = [
        fork \in 1..NP |-> [
            \* We start with each fork held by the lowest-number philosopher
            \* adjacent to the fork.
            holder |-> IF fork = 2 THEN 1 ELSE fork,
            \* Each fork starts out "dirty". Eating causes a fork to become
            \* dirty, after which the philosopher must clean the fork and hand
            \* it to their neighbor.
            clean |-> FALSE
        ]
    ]

define
    LeftFork(p) == p
    RightFork(p) == IF p = NP THEN 1 ELSE p + 1

    LeftPhilosopher(p) == IF p = 1 THEN NP ELSE p - 1
    RightPhilosopher(p) == IF p = NP THEN 1 ELSE p + 1

    IsHoldingBothForks(p) ==
        forks[LeftFork(p)].holder = p /\ forks[RightFork(p)].holder = p
    BothForksAreClean(p) ==
        forks[LeftFork(p)].clean /\ forks[RightFork(p)].clean

    CanEat(p) == IsHoldingBothForks(p) /\ BothForksAreClean(p)
end define;

\* This spawns 'NP' parallel Philosopher processes.
\* 
\* A process looks kind of like an object oriented class, but '\in 1..NP' means
\* it's really just an integer between 1 and NP. Use 'self' to access that
\* integer.
\* 
\* If you remove the 'fair' in 'fair process', each process can stop at any
\* time and will never run again. Dining philosophers don't randomly die while
\* clenching forks in the original problem, so let's keep the processes fair.
fair process Philosopher \in 1..NP
\* This acts like a member variable and you can access it like one. But we're
\* actually creating an array with one element per process, and the "member
\* variable" we access is just the corresponding bucket in that array.
variables hungry = TRUE;
begin
Loop:
    while TRUE do
        \* Check if we're holding dirty forks that other philosophers might
        \* want.
        if
            /\ forks[LeftFork(self)].holder = self
            /\ ~forks[LeftFork(self)].clean
        then
            forks[LeftFork(self)] := [
                holder |-> LeftPhilosopher(self),
                clean |-> TRUE
            ];
        elsif
            /\ forks[RightFork(self)].holder = self
            /\ ~forks[RightFork(self)].clean
        then
            forks[RightFork(self)] := [
                holder |-> RightPhilosopher(self),
                clean |-> TRUE
            ];
        end if;
        if hungry then
            if CanEat(self) then
Eat:
                hungry := FALSE;
                forks[LeftFork(self)].clean := FALSE ||
                forks[RightFork(self)].clean := FALSE;
            end if;
        else
Think:
            hungry := TRUE;
        end if;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ea877089" /\ chksum(tla) = "16352822")
VARIABLES forks, pc

(* define statement *)
LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

LeftPhilosopher(p) == IF p = 1 THEN NP ELSE p - 1
RightPhilosopher(p) == IF p = NP THEN 1 ELSE p + 1

IsHoldingBothForks(p) ==
    forks[LeftFork(p)].holder = p /\ forks[RightFork(p)].holder = p
BothForksAreClean(p) ==
    forks[LeftFork(p)].clean /\ forks[RightFork(p)].clean

CanEat(p) == IsHoldingBothForks(p) /\ BothForksAreClean(p)

VARIABLE hungry

vars == << forks, pc, hungry >>

ProcSet == (1..NP)

Init == (* Global variables *)
        /\ forks =         [
                       fork \in 1..NP |-> [
                   
                   
                           holder |-> IF fork = 2 THEN 1 ELSE fork,
                   
                   
                   
                           clean |-> FALSE
                       ]
                   ]
        (* Process Philosopher *)
        /\ hungry = [self \in 1..NP |-> TRUE]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ IF /\ forks[LeftFork(self)].holder = self
                    /\ ~forks[LeftFork(self)].clean
                    THEN /\ forks' = [forks EXCEPT ![LeftFork(self)] =                          [
                                                                           holder |-> LeftPhilosopher(self),
                                                                           clean |-> TRUE
                                                                       ]]
                    ELSE /\ IF /\ forks[RightFork(self)].holder = self
                               /\ ~forks[RightFork(self)].clean
                               THEN /\ forks' = [forks EXCEPT ![RightFork(self)] =                           [
                                                                                       holder |-> RightPhilosopher(self),
                                                                                       clean |-> TRUE
                                                                                   ]]
                               ELSE /\ TRUE
                                    /\ forks' = forks
              /\ IF hungry[self]
                    THEN /\ IF CanEat(self)
                               THEN /\ pc' = [pc EXCEPT ![self] = "Eat"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Loop"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Think"]
              /\ UNCHANGED hungry

Think(self) == /\ pc[self] = "Think"
               /\ hungry' = [hungry EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "Loop"]
               /\ forks' = forks

Eat(self) == /\ pc[self] = "Eat"
             /\ hungry' = [hungry EXCEPT ![self] = FALSE]
             /\ forks' = [forks EXCEPT ![LeftFork(self)].clean = FALSE,
                                       ![RightFork(self)].clean = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "Loop"]

Philosopher(self) == Loop(self) \/ Think(self) \/ Eat(self)

Next == (\E self \in 1..NP: Philosopher(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NP : WF_vars(Philosopher(self))

\* END TRANSLATION

----
(* Invariant helpers *)
----

(* TRUE iff philosophers p and q share a fork between them. *)
ShareFork(p, q) ==
    {LeftFork(p), RightFork(p)} \cap {LeftFork(q), RightFork(q)} /= {}

----
(* Invariants *)
----

(*
TLA+ and PlusCal are dynamically-typed, but we can roll our own typechecking
with an invariant.
*)
TypeOK ==
    /\ forks \in [1..NP -> [holder: 1..NP, clean: BOOLEAN]]
    /\ hungry \in [1..NP -> BOOLEAN]
    /\ pc \in [1..NP -> {"Loop", "Eat", "Think"}]

(* If two philosophers share a fork, they cannot eat at the same time. *)
ExclusiveAccess ==
    \A p,q \in 1..NP:
        p /= q /\ ShareFork(p, q) => ~(pc[p] = "Eat" /\ pc[q] = "Eat")

----
(* Properties *)
----

(*
Every philosopher will eventually get to eat again.
*)
NobodyStarves == \A p \in 1..NP: []<>(~hungry[p])

====
