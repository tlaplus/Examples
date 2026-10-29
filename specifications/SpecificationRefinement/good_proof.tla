---- MODULE good_proof ----
EXTENDS good, TLAPS

TypeOK ==
  /\ pc \in [Threads -> States]
  /\ counter \in Int
  /\ tmp \in [Threads -> Int]
  /\ lock \in Threads \cup {0}

Inv ==
  /\ TypeOK
  /\ \A t \in Threads :
       /\ (pc[t] = "inc") <=> (lock = t)
       /\ (pc[t] = "inc") => (tmp[t] = counter)

LEMMA TypeAndInv == Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, Threads, States
<1>2. Inv /\ [Next]_vars => Inv'
  BY DEF Inv, TypeOK, Next, vars, Threads, States,
         Trans, GetCounter, IncCounter, AcquireLock, ReleaseLock
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM ImplementsAbstract == Spec => Refinement
<1>1. Init => Mapping!Init
  BY DEF Init, Mapping!Init, Threads, Mapping!Threads
<1>2. Inv /\ [Next]_vars => [Mapping!Next]_Mapping!vars
  BY DEF Inv, TypeOK, Next, vars, Threads, States,
         Trans, GetCounter, IncCounter, AcquireLock, ReleaseLock,
         Mapping!Next, Mapping!vars, Mapping!Trans, Mapping!Threads
<1>3. QED
  BY <1>1, <1>2, TypeAndInv, PTL DEF Spec, Refinement, Mapping!Spec

THEOREM ImplementsBad == Spec => RefinesBad
<1>1. Init => BadMapping!Init
  BY DEF Init, BadMapping!Init, Threads, BadMapping!Threads
<1>2. [Next]_vars => [BadMapping!Next]_BadMapping!vars
  BY DEF Next, vars, Threads, Trans, GetCounter, IncCounter, AcquireLock, ReleaseLock,
         BadMapping!Next, BadMapping!vars, BadMapping!Threads,
         BadMapping!Trans, BadMapping!GetCounter, BadMapping!IncCounter
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec, RefinesBad, BadMapping!Spec

====
