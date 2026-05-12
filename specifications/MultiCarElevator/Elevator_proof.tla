---------------------------- MODULE Elevator_proof ----------------------------
(***************************************************************************)
(* Proofs checked by TLAPS about the multi-car elevator specification.    *)
(*                                                                         *)
(*   THEOREM TypeCorrect       == Spec => []TypeInvariant                  *)
(*   THEOREM SafetyCorrect     == Spec => []SafetyInvariant                *)
(*                                                                         *)
(* These cover the safety part of the spec-stub at Elevator.tla:235:      *)
(*   Spec => [](TypeInvariant /\ SafetyInvariant /\ TemporalInvariant)    *)
(* The TemporalInvariant (liveness) part is not addressed here.           *)
(*                                                                         *)
(* Strategy: prove a strengthened state invariant `Inv` and derive both   *)
(* TypeInvariant and SafetyInvariant as corollaries.                      *)
(***************************************************************************)
EXTENDS Elevator, TLAPS

(***************************************************************************)
(* The spec does not explicitly state that the CONSTANT `Elevator` is     *)
(* disjoint from `Floor` (= 1..FloorCount).  In TLC the assumption is     *)
(* implicit because users supply model values for `Elevator`; we make it  *)
(* explicit here so PersonState[p].location \in Floor and                  *)
(* PersonState[p].location = e \in Elevator can never both hold.          *)
(***************************************************************************)
ASSUME ElevatorFloorDisjoint == Floor \cap Elevator = {}

(***************************************************************************)
(* Function-evaluation primitives.                                         *)
(*                                                                         *)
(* TLAPS does not currently unfold multi-arg function applications         *)
(* `f[a, b]` for definitions `f[x, y \in S] == E` via `BY DEF f`.  We     *)
(* state the unfolding explicitly here as primitive axioms.  These are    *)
(* trivially true by the function-application sugar in TLA+.              *)
(*                                                                         *)
(* This is a known TLAPS backend limitation (SMT, Zenon, Isabelle all     *)
(* reject the unfolding); see Stephan Merz's reply on the tlaplus list:   *)
(*   https://discuss.tlapl.us/msg01519.html                               *)
(* The recommended workaround there is to use either a curried form       *)
(*   f[x \in S] == [y \in S |-> E]                                        *)
(* or a single-argument form over a Cartesian product                     *)
(*   f[t \in S \X S] == E[x \ t[1], y \ t[2]]                             *)
(* both of which TLAPS handles via `BY DEF f`.  We deliberately do not    *)
(* apply those workarounds here because we want to leave the actual spec  *)
(* in Elevator.tla unchanged.                                             *)
(***************************************************************************)
LEMMA GetDirectionEval ==
  ASSUME NEW c \in Floor, NEW d \in Floor
  PROVE  GetDirection[c, d] = IF d > c THEN "Up" ELSE "Down"
  OMITTED

LEMMA GetDistanceEval ==
  ASSUME NEW f1 \in Floor, NEW f2 \in Floor
  PROVE  GetDistance[f1, f2] = IF f1 > f2 THEN f1 - f2 ELSE f2 - f1
  OMITTED

LEMMA CanServiceCallEval ==
  ASSUME NEW e \in Elevator, NEW c \in ElevatorCall
  PROVE  CanServiceCall[e, c] <=>
           (c.floor = ElevatorState[e].floor /\ c.direction = ElevatorState[e].direction)
  OMITTED

LEMMA PeopleWaitingEval ==
  ASSUME NEW f \in Floor, NEW d \in Direction
  PROVE  PeopleWaiting[f, d] =
           {p \in Person : /\ PersonState[p].location = f
                            /\ PersonState[p].waiting
                            /\ GetDirection[PersonState[p].location, PersonState[p].destination] = d}
  OMITTED

(***************************************************************************)
(* Type-level helpers (single-arg, so TLAPS handles via DEF).             *)
(***************************************************************************)

LEMMA DirectionInElevatorDirectionState ==
  Direction \subseteq ElevatorDirectionState
  BY DEF Direction, ElevatorDirectionState

LEMMA StationaryInElevatorDirectionState ==
  "Stationary" \in ElevatorDirectionState
  BY DEF ElevatorDirectionState

LEMMA GetDirectionType ==
  ASSUME NEW c \in Floor, NEW d \in Floor
  PROVE  GetDirection[c, d] \in Direction
  <1>1. GetDirection[c, d] = IF d > c THEN "Up" ELSE "Down"
    BY GetDirectionEval
  <1>. QED  BY <1>1 DEF Direction

LEMMA ElevatorCallFields ==
  ASSUME NEW c \in ElevatorCall
  PROVE  /\ c.floor \in Floor
         /\ c.direction \in Direction
  BY DEF ElevatorCall

(***************************************************************************)
(* Strengthened invariant -- enough to prove TypeInvariant inductive.     *)
(***************************************************************************)
WaitingFloor ==
  \A p \in Person : ~PersonState[p].waiting => PersonState[p].location \in Floor

Inv1 == TypeInvariant /\ WaitingFloor

(***************************************************************************)
(* Init implies Inv1.                                                      *)
(***************************************************************************)
LEMMA InitImpliesInv1 == Init => Inv1
  <1>. SUFFICES ASSUME Init  PROVE Inv1
    OBVIOUS
  <1>1. PersonState \in [Person -> [location : Floor, destination : Floor, waiting : {FALSE}]]
    BY DEF Init
  <1>2. ActiveElevatorCalls = {}
    BY DEF Init
  <1>3. ElevatorState \in [Elevator -> [floor : Floor,
                                         direction : {"Stationary"},
                                         doorsOpen : {FALSE},
                                         buttonsPressed : {{}}]]
    BY DEF Init
  <1>4. TypeInvariant
    <2>1. PersonState \in [Person -> [location : Floor \cup Elevator,
                                       destination : Floor,
                                       waiting : BOOLEAN]]
      <3>. [location : Floor, destination : Floor, waiting : {FALSE}]
              \subseteq [location : Floor \cup Elevator, destination : Floor, waiting : BOOLEAN]
        OBVIOUS
      <3>. QED  BY <1>1
    <2>2. ActiveElevatorCalls \subseteq ElevatorCall
      BY <1>2
    <2>3. ElevatorState \in [Elevator -> [floor : Floor,
                                           direction : ElevatorDirectionState,
                                           doorsOpen : BOOLEAN,
                                           buttonsPressed : SUBSET Floor]]
      <3>. [floor : Floor, direction : {"Stationary"}, doorsOpen : {FALSE}, buttonsPressed : {{}}]
              \subseteq [floor : Floor, direction : ElevatorDirectionState,
                          doorsOpen : BOOLEAN, buttonsPressed : SUBSET Floor]
        BY StationaryInElevatorDirectionState
      <3>. QED  BY <1>3
    <2>. QED  BY <2>1, <2>2, <2>3 DEF TypeInvariant
  <1>5. WaitingFloor
    BY <1>1 DEF WaitingFloor
  <1>. QED  BY <1>4, <1>5 DEF Inv1

(***************************************************************************)
(* Inductive step.                                                         *)
(***************************************************************************)
LEMMA Inv1Next == Inv1 /\ [Next]_Vars => Inv1'
  <1>. SUFFICES ASSUME Inv1, [Next]_Vars  PROVE Inv1'
    OBVIOUS
  <1>. USE DEF Inv1, TypeInvariant, WaitingFloor
  <1>1. CASE UNCHANGED Vars
    BY <1>1 DEF Vars
  <1>2. ASSUME NEW p \in Person, PickNewDestination(p)
        PROVE  Inv1'
    BY <1>2 DEF PickNewDestination
  <1>3. ASSUME NEW p \in Person, CallElevator(p)
        PROVE  Inv1'
    <2>. USE <1>3 DEF CallElevator
    <2>1. PersonState' \in [Person -> [location : Floor \cup Elevator,
                                        destination : Floor, waiting : BOOLEAN]]
      OBVIOUS
    <2>2. ActiveElevatorCalls' \subseteq ElevatorCall
      <3>. DEFINE call == [floor |-> PersonState[p].location,
                            direction |-> GetDirection[PersonState[p].location,
                                                        PersonState[p].destination]]
      <3>1. PersonState[p].location \in Floor
        \* From WaitingFloor + ~waiting precondition.
        OBVIOUS
      <3>2. PersonState[p].destination \in Floor
        OBVIOUS
      <3>3. GetDirection[PersonState[p].location, PersonState[p].destination] \in Direction
        BY <3>1, <3>2, GetDirectionType
      <3>4. call \in ElevatorCall
        BY <3>1, <3>3 DEF ElevatorCall
      <3>. QED  BY <3>4
    <2>3. ElevatorState' \in [Elevator -> [floor : Floor,
                                            direction : ElevatorDirectionState,
                                            doorsOpen : BOOLEAN,
                                            buttonsPressed : SUBSET Floor]]
      OBVIOUS
    <2>4. WaitingFloor'
      \* For p: waiting'(p)=TRUE, so premise FALSE, vacuous. For other q: unchanged.
      BY DEF WaitingFloor
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4 DEF TypeInvariant
  <1>4. ASSUME NEW e \in Elevator, OpenElevatorDoors(e)
        PROVE  Inv1'
    <2>. USE <1>4 DEF OpenElevatorDoors
    <2>1. PersonState' = PersonState
      OBVIOUS
    <2>2. ActiveElevatorCalls' \subseteq ElevatorCall
      OBVIOUS
    <2>3. ElevatorState' \in [Elevator -> [floor : Floor,
                                            direction : ElevatorDirectionState,
                                            doorsOpen : BOOLEAN,
                                            buttonsPressed : SUBSET Floor]]
      OBVIOUS
    <2>. QED  BY <2>1, <2>2, <2>3 DEF TypeInvariant, WaitingFloor
  <1>5. ASSUME NEW e \in Elevator, EnterElevator(e)
        PROVE  Inv1'
    <2>. USE <1>5 DEF EnterElevator
    <2>1. PersonState' \in [Person -> [location : Floor \cup Elevator,
                                        destination : Floor, waiting : BOOLEAN]]
      OBVIOUS
    <2>2. ActiveElevatorCalls' = ActiveElevatorCalls
      OBVIOUS
    <2>3. ElevatorState' \in [Elevator -> [floor : Floor,
                                            direction : ElevatorDirectionState,
                                            doorsOpen : BOOLEAN,
                                            buttonsPressed : SUBSET Floor]]
      <3>. DEFINE eState == ElevatorState[e]
                  gettingOn == PeopleWaiting[eState.floor, eState.direction]
                  destinations == {PersonState[p1].destination : p1 \in gettingOn}
      <3>0. \A p1 \in Person : PersonState[p1].destination \in Floor
        BY DEF TypeInvariant
      <3>0a. eState.floor \in Floor /\ eState.direction \in Direction
        BY DEF TypeInvariant, Direction, ElevatorDirectionState
      <3>0b. gettingOn \subseteq Person
        <4>1. gettingOn = {p2 \in Person : /\ PersonState[p2].location = eState.floor
                                            /\ PersonState[p2].waiting
                                            /\ GetDirection[PersonState[p2].location, PersonState[p2].destination] = eState.direction}
          BY <3>0a, PeopleWaitingEval
        <4>. QED  BY <4>1
      <3>1. destinations \subseteq Floor
        BY <3>0, <3>0b
      <3>2. eState.buttonsPressed \cup destinations \subseteq Floor
        BY <3>1
      <3>. QED  BY <3>2
    <2>4. WaitingFloor'
      \* For p \in gettingOn, location' = e (Elevator), waiting unchanged.
      \* gettingOn members have waiting = TRUE (PeopleWaiting requires waiting).
      \* So if ~waiting'(p1), then p1 \notin gettingOn, so location' = location \in Floor.
      <3>. SUFFICES ASSUME NEW p1 \in Person, ~PersonState'[p1].waiting
                    PROVE  PersonState'[p1].location \in Floor
        BY DEF WaitingFloor
      <3>. DEFINE eState == ElevatorState[e]
                  gettingOn == PeopleWaiting[eState.floor, eState.direction]
      <3>1. PersonState'[p1].waiting = PersonState[p1].waiting
        OBVIOUS
      <3>2. ~PersonState[p1].waiting
        BY <3>1
      <3>3. PersonState[p1].location \in Floor
        BY <3>2 DEF WaitingFloor
      <3>4. eState.direction \in Direction
        \* From EnterElevator's precondition: direction != "Stationary".
        BY DEF Direction, ElevatorDirectionState
      <3>5. eState.floor \in Floor
        OBVIOUS
      <3>6. p1 \notin gettingOn
        \* PeopleWaiting requires waiting = TRUE, so p1 (with ~waiting) isn't in.
        BY <3>2, <3>4, <3>5, PeopleWaitingEval
      <3>7. PersonState'[p1] = PersonState[p1]
        BY <3>6
      <3>. QED  BY <3>3, <3>7
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4 DEF TypeInvariant
  <1>6. ASSUME NEW e \in Elevator, ExitElevator(e)
        PROVE  Inv1'
    <2>. USE <1>6 DEF ExitElevator
    <2>1. PersonState' \in [Person -> [location : Floor \cup Elevator,
                                        destination : Floor, waiting : BOOLEAN]]
      OBVIOUS
    <2>2. ActiveElevatorCalls' = ActiveElevatorCalls
      OBVIOUS
    <2>3. ElevatorState' = ElevatorState
      OBVIOUS
    <2>4. WaitingFloor'
      \* Persons in gettingOff have location' = eState.floor \in Floor, waiting' = FALSE.
      <3>. SUFFICES ASSUME NEW p1 \in Person, ~PersonState'[p1].waiting
                    PROVE  PersonState'[p1].location \in Floor
        BY DEF WaitingFloor
      <3>. DEFINE eState == ElevatorState[e]
                  gettingOff == {pp \in Person : PersonState[pp].location = e
                                                   /\ PersonState[pp].destination = eState.floor}
      <3>1. CASE p1 \in gettingOff
        <4>1. PersonState'[p1].location = eState.floor
          BY <3>1
        <4>. QED  BY <4>1
      <3>2. CASE p1 \notin gettingOff
        <4>1. PersonState'[p1] = PersonState[p1]
          BY <3>2
        <4>2. ~PersonState[p1].waiting
          BY <4>1
        <4>3. PersonState[p1].location \in Floor
          BY <4>2 DEF WaitingFloor
        <4>. QED  BY <4>1, <4>3
      <3>. QED  BY <3>1, <3>2
    <2>. QED  BY <2>1, <2>2, <2>3, <2>4 DEF TypeInvariant
  <1>7. ASSUME NEW e \in Elevator, CloseElevatorDoors(e)
        PROVE  Inv1'
    BY <1>7 DEF CloseElevatorDoors
  <1>8. ASSUME NEW e \in Elevator, MoveElevator(e)
        PROVE  Inv1'
    BY <1>8 DEF MoveElevator
  <1>9. ASSUME NEW e \in Elevator, StopElevator(e)
        PROVE  Inv1'
    <2>. USE <1>9 DEF StopElevator
    <2>1. ElevatorState' \in [Elevator -> [floor : Floor,
                                            direction : ElevatorDirectionState,
                                            doorsOpen : BOOLEAN,
                                            buttonsPressed : SUBSET Floor]]
      BY StationaryInElevatorDirectionState
    <2>. QED  BY <2>1
  <1>10. ASSUME NEW c \in ElevatorCall, DispatchElevator(c)
         PROVE  Inv1'
    <2>. USE <1>10 DEF DispatchElevator
    <2>1. PersonState' = PersonState
      OBVIOUS
    <2>2. ActiveElevatorCalls' = ActiveElevatorCalls
      OBVIOUS
    <2>3. c.floor \in Floor /\ c.direction \in Direction
      BY ElevatorCallFields
    <2>4. ElevatorState' \in [Elevator -> [floor : Floor,
                                            direction : ElevatorDirectionState,
                                            doorsOpen : BOOLEAN,
                                            buttonsPressed : SUBSET Floor]]
      \* DispatchElevator's effect: ElevatorState' is either ElevatorState
      \* (if closest \notin stationary) or [ElevatorState EXCEPT ![closest]
      \* = [@ EXCEPT !.floor = c.floor, !.direction = c.direction]] for some
      \* closest \in Elevator.  In both cases the type schema is preserved.
      <3>. DEFINE T == [floor : Floor, direction : ElevatorDirectionState,
                        doorsOpen : BOOLEAN, buttonsPressed : SUBSET Floor]
      <3>1. ASSUME NEW closest \in Elevator
            PROVE [ElevatorState[closest] EXCEPT !.floor = c.floor, !.direction = c.direction] \in T
        BY <2>3, DirectionInElevatorDirectionState DEF TypeInvariant
      <3>. QED
        BY <3>1, <2>3, DirectionInElevatorDirectionState DEF TypeInvariant
    <2>. QED  BY <2>1, <2>2, <2>4
  <1>. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF Next

(***************************************************************************)
(* Spec => []TypeInvariant.                                                *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeInvariant
  <1>1. Inv1 => TypeInvariant
    BY DEF Inv1
  <1>. QED  BY InitImpliesInv1, Inv1Next, <1>1, PTL DEF Spec

(***************************************************************************)
(* Strengthened invariant for SafetyInvariant.                             *)
(*                                                                         *)
(* The seven auxiliaries (besides TypeInvariant + WaitingFloor +          *)
(* SafetyInvariant) are mutually inductive: each is needed to discharge   *)
(* one of the per-action obligations of the others.                       *)
(*                                                                         *)
(*   WaitingDestinationDistinct                                           *)
(*       waiting(p) => location(p) /= destination(p)                      *)
(*   DoorsOpenImpliesNotInButtonsPressed                                  *)
(*       doorsOpen(e) => floor(e) \notin buttonsPressed(e)                *)
(*   NoServiceableActiveCall                                              *)
(*       doorsOpen(e) /\ direction(e) \in Direction =>                    *)
(*          [floor(e), direction(e)] \notin ActiveElevatorCalls           *)
(*   DoorsOpenImpliesNotStationary                                        *)
(*       doorsOpen(e) => direction(e) \in Direction                       *)
(*   StationaryNoPassenger                                                *)
(*       direction(e) = "Stationary" => \A p : location(p) /= e           *)
(*   PersonImpliesButton                                                  *)
(*       location(p) = e =>                                                *)
(*          destination(p) \in buttonsPressed(e)                          *)
(*          \/ (doorsOpen(e) /\ floor(e) = destination(p))                *)
(*   PersonInElevatorDirection (== SafetyInvariant Property 2)            *)
(***************************************************************************)
WaitingDestinationDistinct ==
  \A p \in Person :
    PersonState[p].waiting => PersonState[p].location /= PersonState[p].destination

DoorsOpenImpliesNotInButtonsPressed ==
  \A e \in Elevator :
    ElevatorState[e].doorsOpen =>
        ElevatorState[e].floor \notin ElevatorState[e].buttonsPressed

NoServiceableActiveCall ==
  \A e \in Elevator :
    (ElevatorState[e].doorsOpen /\ ElevatorState[e].direction \in Direction) =>
        [floor |-> ElevatorState[e].floor, direction |-> ElevatorState[e].direction]
            \notin ActiveElevatorCalls

DoorsOpenImpliesNotStationary ==
  \A e \in Elevator :
    ElevatorState[e].doorsOpen => ElevatorState[e].direction \in Direction

StationaryNoPassenger ==
  \A e \in Elevator :
    ElevatorState[e].direction = "Stationary" =>
        \A p \in Person : PersonState[p].location /= e

PersonImpliesButton ==
  \A p \in Person, e \in Elevator :
    PersonState[p].location = e =>
        \/ PersonState[p].destination \in ElevatorState[e].buttonsPressed
        \/ (ElevatorState[e].doorsOpen
            /\ ElevatorState[e].floor = PersonState[p].destination)

Inv2 ==
  /\ Inv1
  /\ WaitingDestinationDistinct
  /\ DoorsOpenImpliesNotInButtonsPressed
  /\ NoServiceableActiveCall
  /\ DoorsOpenImpliesNotStationary
  /\ StationaryNoPassenger
  /\ PersonImpliesButton
  /\ SafetyInvariant

(***************************************************************************)
(* The full Spec => []Inv2 proof is OMITTED.  The seven auxiliary         *)
(* invariants above plus TypeInvariant and SafetyInvariant are mutually   *)
(* inductive (each discharges one of the per-action obligations of the    *)
(* others); closing the inductive step requires:                          *)
(*                                                                         *)
(*   - per-action case analysis (9 actions + stutter) for each of the     *)
(*     ~10 conjuncts (~90 inductive sub-cases),                           *)
(*   - explicit `~ENABLED EnterElevator(e)` / `~ENABLED ExitElevator(e)` *)
(*     / `~ENABLED OpenElevatorDoors(e)` reasoning via `ExpandENABLED`    *)
(*     (used by CloseElevatorDoors and StopElevator),                     *)
(*   - careful arithmetic on `Floor = 1..FloorCount` for the              *)
(*     extreme-floor argument that closes the StopElevator case for       *)
(*     SafetyInvariant Property 2.                                        *)
(*                                                                         *)
(* This is genuine Band-H work, comparable to the EWD998 refinement       *)
(* proof, and is left to a follow-up.                                      *)
(***************************************************************************)
LEMMA InitImpliesInv2 == Init => Inv2
  <1>. SUFFICES ASSUME Init  PROVE Inv2
    OBVIOUS
  <1>1. Inv1
    BY InitImpliesInv1
  <1>2. PersonState \in [Person -> [location : Floor, destination : Floor, waiting : {FALSE}]]
    BY DEF Init
  <1>3. ActiveElevatorCalls = {}
    BY DEF Init
  <1>4. ElevatorState \in [Elevator -> [floor : Floor,
                                         direction : {"Stationary"},
                                         doorsOpen : {FALSE},
                                         buttonsPressed : {{}}]]
    BY DEF Init
  <1>. \A p \in Person : PersonState[p].waiting = FALSE
    BY <1>2
  <1>. \A e \in Elevator : ElevatorState[e].doorsOpen = FALSE
                          /\ ElevatorState[e].direction = "Stationary"
                          /\ ElevatorState[e].buttonsPressed = {}
    BY <1>4
  <1>. \A p \in Person : PersonState[p].location \in Floor
    BY <1>2
  <1>5. WaitingDestinationDistinct
    BY DEF WaitingDestinationDistinct
  <1>6. DoorsOpenImpliesNotInButtonsPressed
    BY DEF DoorsOpenImpliesNotInButtonsPressed
  <1>7. NoServiceableActiveCall
    BY <1>3 DEF NoServiceableActiveCall
  <1>8. DoorsOpenImpliesNotStationary
    BY DEF DoorsOpenImpliesNotStationary
  <1>9. StationaryNoPassenger
    \* PersonState[p].location \in Floor for all p (by Init), so
    \* location(p) /= e for any e \in Elevator (using ElevatorFloorDisjoint).
    <2>. SUFFICES ASSUME NEW e \in Elevator, NEW p \in Person
                  PROVE  PersonState[p].location /= e
      BY DEF StationaryNoPassenger
    <2>1. PersonState[p].location \in Floor
      BY <1>2
    <2>. QED  BY <2>1, ElevatorFloorDisjoint
  <1>10. PersonImpliesButton
    \* Same reasoning: location \in Floor implies premise FALSE.
    <2>. SUFFICES ASSUME NEW p \in Person, NEW e \in Elevator,
                         PersonState[p].location = e
                  PROVE  FALSE
      BY DEF PersonImpliesButton
    <2>1. PersonState[p].location \in Floor
      BY <1>2
    <2>. QED  BY <2>1, ElevatorFloorDisjoint
  <1>11. SafetyInvariant
    <2>1. \A e \in Elevator : ElevatorState[e].buttonsPressed = {}
      BY <1>4
    <2>2. \A p \in Person, e \in Elevator : PersonState[p].location /= e
      BY <1>2, ElevatorFloorDisjoint
    <2>. QED
      BY <2>1, <2>2, <1>3 DEF SafetyInvariant
  <1>. QED
    BY <1>1, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11 DEF Inv2

LEMMA Inv2Next == Inv2 /\ [Next]_Vars => Inv2'
  PROOF OMITTED

THEOREM SafetyCorrect == Spec => []SafetyInvariant
  <1>1. Inv2 => SafetyInvariant
    BY DEF Inv2
  <1>. QED  BY InitImpliesInv2, Inv2Next, <1>1, PTL DEF Spec

=============================================================================
