---------------------------- MODULE CoffeeCan -------------------------------

EXTENDS Naturals, Integers

VARIABLES can

Can == [black : Nat, white : Int]

\* Initialize can so it contains at least one bean.
Init == can \in {c \in Can : c.black + c.white >= 1}

BeanCount == can.black + can.white

PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

EventuallyTerminates == <>(ENABLED Termination)

MonotonicDecrease == [][BeanCount > 1 => BeanCount' < BeanCount]_<<can>>

WhiteBeanTermination ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)

FinalBeanColor ==
    can.white 

Spec ==
    /\ Init
    /\ [][Next]_<<can>>
    /\ WF_<<can>>(Next)

THEOREM Spec =>
    /\ EventuallyTerminates
    /\ MonotonicDecrease
    /\ WhiteBeanTermination

=============================================================================
