------------------------------ MODULE Elevator ------------------------------
(***************************************************************************)
(* This spec describes a simple multi-car elevator system. The actions in  *)
(* this spec are unsurprising and common to all such systems except for    *)
(* DispatchElevator, which contains the logic to determine which elevator  *)
(* ought to service which call. The algorithm used is very simple and does *)
(* not optimize for global throughput or average wait time. The            *)
(* TemporalInvariant definition ensures this specification provides        *)
(* capabilities expected of any elevator system, such as people eventually *)
(* reaching their destination floor.                                       *)
(***************************************************************************)

EXTENDS     Integers

CONSTANTS   Person,     \* The set of all people using the elevator system
            Elevator,   \* The set of all elevators
            FloorCount  \* The number of floors serviced by the elevator system

VARIABLES   PersonState,            \* The state of each person
            ActiveElevatorCalls,    \* The set of all active elevator calls
            ElevatorState           \* The state of each elevator

Vars == \* Tuple of all specification variables
    <<PersonState, ActiveElevatorCalls, ElevatorState>>

Floor ==    \* The set of all floors
    1 .. FloorCount

Direction ==    \* Directions available to this elevator system
    {"Up", "Down"}

ElevatorCall == \* The set of all elevator calls
    [floor : Floor, direction : Direction]

ElevatorDirectionState ==   \* Elevator movement state; it is either moving in a direction or stationary
    Direction \cup {"Stationary"}

GetDistance[f1, f2 \in Floor] ==    \* The distance between two floors
    IF f1 > f2 THEN f1 - f2 ELSE f2 - f1
    
GetDirection[current, destination \in Floor] == \* Direction of travel required to move between current and destination floors
    IF destination > current THEN "Up" ELSE "Down"

CanServiceCall[e \in Elevator, c \in ElevatorCall] ==   \* Whether elevator is in position to immediately service call
    LET eState == ElevatorState[e] IN
    /\ c.floor = eState.floor
    /\ c.direction = eState.direction

PeopleWaiting[f \in Floor, d \in Direction] ==  \* The set of all people waiting on an elevator call
    {p \in Person :
        /\ PersonState[p].location = f
        /\ PersonState[p].waiting
        /\ GetDirection[PersonState[p].location, PersonState[p].destination] = d}

TypeInvariant ==    \* Statements about the variables which we expect to hold in every system state
    /\ PersonState \in [Person -> [location : Floor \cup Elevator, destination : Floor, waiting : BOOLEAN]]
    /\ ActiveElevatorCalls \subseteq ElevatorCall
    /\ ElevatorState \in [Elevator -> [floor : Floor, direction : ElevatorDirectionState, doorsOpen : BOOLEAN, buttonsPressed : SUBSET Floor]]

SafetyInvariant ==   \* Some more comprehensive checks beyond the type invariant
    /\ \A e \in Elevator :  \* An elevator has a floor button pressed only if a person in that elevator is going to that floor
        /\ \A f \in ElevatorState[e].buttonsPressed :
            /\ \E p \in Person :
                /\ PersonState[p].location = e
                /\ PersonState[p].destination = f
    /\ \A p \in Person :    \* A person is in an elevator only if the elevator is moving toward their destination floor
        /\ \A e \in Elevator :
            /\ (PersonState[p].location = e /\ ElevatorState[e].floor /= PersonState[p].destination) => 
                /\ ElevatorState[e].direction = GetDirection[ElevatorState[e].floor, PersonState[p].destination]
    /\ \A c \in ActiveElevatorCalls : PeopleWaiting[c.floor, c.direction] /= {} \* No ghost calls

TemporalInvariant ==  \* Expectations about elevator system capabilities
    /\ \A c \in ElevatorCall :  \* Every call is eventually serviced by an elevator
        /\ c \in ActiveElevatorCalls ~> \E e \in Elevator : CanServiceCall[e, c]
    /\ \A p \in Person :    \* If a person waits for their elevator, they'll eventually arrive at their floor
        /\ PersonState[p].waiting ~> PersonState[p].location = PersonState[p].destination

PickNewDestination(p) ==    \* Person decides they need to go to a different floor
    LET pState == PersonState[p] IN
    /\ ~pState.waiting
    /\ pState.location \in Floor
    /\ \E f \in Floor :
        /\ f /= pState.location
        /\ PersonState' = [PersonState EXCEPT ![p] = [@ EXCEPT !.destination = f]]
    /\ UNCHANGED <<ActiveElevatorCalls, ElevatorState>>

CallElevator(p) ==  \* Person calls the elevator to go in a certain direction from their floor
    LET
      pState == PersonState[p]
      call == [floor |-> pState.location, direction |-> GetDirection[pState.location, pState.destination]]
    IN
    /\ ~pState.waiting
    /\ pState.location /= pState.destination
    /\ ActiveElevatorCalls' =
        IF \E e \in Elevator :
            /\ CanServiceCall[e, call]
            /\ ElevatorState[e].doorsOpen
        THEN ActiveElevatorCalls
        ELSE ActiveElevatorCalls \cup {call}
    /\ PersonState' = [PersonState EXCEPT ![p] = [@ EXCEPT !.waiting = TRUE]]
    /\ UNCHANGED <<ElevatorState>>

OpenElevatorDoors(e) == \* Open the elevator doors if there is a call on this floor or the button for this floor was pressed.
    LET eState == ElevatorState[e] IN
    /\ ~eState.doorsOpen
    /\  \/ \E call \in ActiveElevatorCalls : CanServiceCall[e, call]
        \/ eState.floor \in eState.buttonsPressed
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.doorsOpen = TRUE, !.buttonsPressed = @ \ {eState.floor}]]
    /\ ActiveElevatorCalls' = ActiveElevatorCalls \ {[floor |-> eState.floor, direction |-> eState.direction]}
    /\ UNCHANGED <<PersonState>>
    
EnterElevator(e) == \* All people on this floor who are waiting for the elevator and travelling the same direction enter the elevator.
    LET
      eState == ElevatorState[e]
      gettingOn == PeopleWaiting[eState.floor, eState.direction]
      destinations == {PersonState[p].destination : p \in gettingOn}
    IN
    /\ eState.doorsOpen
    /\ eState.direction /= "Stationary"
    /\ gettingOn /= {}
    /\ PersonState' = [p \in Person |->
        IF p \in gettingOn
        THEN [PersonState[p] EXCEPT !.location = e]
        ELSE PersonState[p]]
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.buttonsPressed = @ \cup destinations]]
    /\ UNCHANGED <<ActiveElevatorCalls>>

ExitElevator(e) ==  \* All people whose destination is this floor exit the elevator.
    LET
      eState == ElevatorState[e]
      gettingOff == {p \in Person : PersonState[p].location = e /\ PersonState[p].destination = eState.floor}
    IN
    /\ eState.doorsOpen
    /\ gettingOff /= {}
    /\ PersonState' = [p \in Person |->
        IF p \in gettingOff
        THEN [PersonState[p] EXCEPT !.location = eState.floor, !.waiting = FALSE]
        ELSE PersonState[p]]
    /\ UNCHANGED <<ActiveElevatorCalls, ElevatorState>>

CloseElevatorDoors(e) ==    \* Close the elevator doors once all people have entered and exited the elevator on this floor.
    LET eState == ElevatorState[e] IN
    /\ ~ENABLED EnterElevator(e)
    /\ ~ENABLED ExitElevator(e)
    /\ eState.doorsOpen
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.doorsOpen = FALSE]]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

MoveElevator(e) ==  \* Move the elevator to the next floor unless we have to open the doors here.
    LET
      eState == ElevatorState[e]
      nextFloor == IF eState.direction = "Up" THEN eState.floor + 1 ELSE eState.floor - 1
    IN
    /\ eState.direction /= "Stationary"
    /\ ~eState.doorsOpen
    /\ eState.floor \notin eState.buttonsPressed
    /\ \A call \in ActiveElevatorCalls : \* Can move only if other elevator servicing call
        /\ CanServiceCall[e, call] =>
            /\ \E e2 \in Elevator :
                /\ e /= e2
                /\ CanServiceCall[e2, call]
    /\ nextFloor \in Floor
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.floor = nextFloor]]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

StopElevator(e) == \* Stops the elevator if it's moved as far as it can in one direction
    LET
      eState == ElevatorState[e]
      nextFloor == IF eState.direction = "Up" THEN eState.floor + 1 ELSE eState.floor - 1
    IN
    /\ ~ENABLED OpenElevatorDoors(e)
    /\ ~eState.doorsOpen
    /\ nextFloor \notin Floor
    /\ ElevatorState' = [ElevatorState EXCEPT ![e] = [@ EXCEPT !.direction = "Stationary"]]
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

(***************************************************************************)
(* This action chooses an elevator to service the call. The simple         *)
(* algorithm picks the closest elevator which is either stationary or      *)
(* already moving toward the call floor in the same direction as the call. *)
(* The system keeps no record of assigning an elevator to service a call.  *)
(* It is possible no elevator is able to service a call, but we are        *)
(* guaranteed an elevator will eventually become available.                *)
(***************************************************************************)
DispatchElevator(c) ==
    LET
      stationary == {e \in Elevator : ElevatorState[e].direction = "Stationary"}
      approaching == {e \in Elevator :
        /\ ElevatorState[e].direction = c.direction
        /\  \/ ElevatorState[e].floor = c.floor
            \/ GetDirection[ElevatorState[e].floor, c.floor] = c.direction }
    IN
    /\ c \in ActiveElevatorCalls
    /\ stationary \cup approaching /= {}
    /\ ElevatorState' = 
        LET closest == CHOOSE e \in stationary \cup approaching :
            /\ \A e2 \in stationary \cup approaching :
                /\ GetDistance[ElevatorState[e].floor, c.floor] <= GetDistance[ElevatorState[e2].floor, c.floor] IN
        IF closest \in stationary
        THEN [ElevatorState EXCEPT ![closest] = [@ EXCEPT !.floor = c.floor, !.direction = c.direction]]
        ELSE ElevatorState
    /\ UNCHANGED <<PersonState, ActiveElevatorCalls>>

Init == \* Initializes people and elevators to arbitrary floors
    /\ PersonState \in [Person -> [location : Floor, destination : Floor, waiting : {FALSE}]]
    /\ ActiveElevatorCalls = {}
    /\ ElevatorState \in [Elevator -> [floor : Floor, direction : {"Stationary"}, doorsOpen : {FALSE}, buttonsPressed : {{}}]]

Next == \* The next-state relation
    \/ \E p \in Person : PickNewDestination(p)
    \/ \E p \in Person : CallElevator(p)
    \/ \E e \in Elevator : OpenElevatorDoors(e)
    \/ \E e \in Elevator : EnterElevator(e)
    \/ \E e \in Elevator : ExitElevator(e)
    \/ \E e \in Elevator : CloseElevatorDoors(e)
    \/ \E e \in Elevator : MoveElevator(e)
    \/ \E e \in Elevator : StopElevator(e)
    \/ \E c \in ElevatorCall : DispatchElevator(c)

TemporalAssumptions ==  \* Assumptions about how elevators and people will behave
    /\ \A p \in Person : WF_Vars(CallElevator(p))
    /\ \A e \in Elevator : WF_Vars(OpenElevatorDoors(e))
    /\ \A e \in Elevator : WF_Vars(EnterElevator(e))
    /\ \A e \in Elevator : WF_Vars(ExitElevator(e))
    /\ \A e \in Elevator : SF_Vars(CloseElevatorDoors(e))
    /\ \A e \in Elevator : SF_Vars(MoveElevator(e))
    /\ \A e \in Elevator : WF_Vars(StopElevator(e))
    /\ \A c \in ElevatorCall : SF_Vars(DispatchElevator(c))

Spec == \* Initialize state with Init and transition with Next, subject to TemporalAssumptions
    /\ Init
    /\ [][Next]_Vars
    /\ TemporalAssumptions

THEOREM Spec => [](TypeInvariant /\ SafetyInvariant /\ TemporalInvariant)

=============================================================================

