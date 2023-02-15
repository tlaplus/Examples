---------------------------- MODULE product ----------------------------

\* Now that we can cycle properly and also count...
\* let's look at the actual "product" of the process.
\* This requires more variables, for a hi-res view.


EXTENDS Naturals, Sequences \* imports

CONSTANTS DNA, PRIMER \* starting stock of key things

VARIABLES tee, 
          stage, 
          cycle, 
          primer, 
          (* and single-stranded templates *)
          longTemplate,
          shortTemplate,
          tinyTemplate,
          (* and the hybrids *)
          longHybrid,
          shortHybrid,
          tinyHybrid,
          (* and double strands *)
          longLongDouble,
          shortLongDouble,
          tinyShortDouble,          
          (* and the product *)
          product \* a tinyTiny double, if you prefer

(* list of state variables *)
vars == <<tee, \* temperature
          stage, \* a history, if you think about it
          cycle, \* we can count
          primer,
          (* and single-stranded templates *)
          longTemplate,
          shortTemplate,
          tinyTemplate,
          (* and the hybrids *)
          longHybrid,
          shortHybrid,
          tinyHybrid,          
          (* and doubles *)
          longLongDouble,
          shortLongDouble,
          tinyShortDouble,                    
          (* and the product *)
          product
        >>  
        
(* more variable lists, for convenience *)
templates == <<longTemplate,
               shortTemplate,
               tinyTemplate>>
                    
hybrids == <<longHybrid,
             shortHybrid,
             tinyHybrid>>
                        
doubles == <<longLongDouble,
             shortLongDouble,
             tinyShortDouble,
             product>>

(* helper functions *)
natMin(i,j) == IF i < j THEN i ELSE j \* min of two nats
RECURSIVE sumList(_) \* sum of a list
sumList(s) == IF s = <<>> THEN 0 ELSE Head(s) + sumList(Tail(s))

(* actions *)
heat ==    /\ tee = "Hot" \* current temperature is "Hot"
           /\ tee' = "TooHot" \* heat up to "TooHot"
           /\ primer' = primer + sumList(hybrids) \* recover primers from hybrids
           (* double strands denature *)
           /\ longLongDouble' = 0
           /\ shortLongDouble' = 0
           /\ tinyShortDouble' = 0
           /\ product' = 0
           (* hybrids denature *)
           /\ longHybrid' = 0
           /\ shortHybrid' = 0
           /\ tinyHybrid' = 0
           (* templates absorb all this*)
           /\ longTemplate' = longTemplate + longHybrid + shortLongDouble + 2 * longLongDouble \* only place they come from
           /\ shortTemplate' = shortTemplate + shortHybrid + shortLongDouble + tinyShortDouble
           /\ tinyTemplate' = tinyTemplate + tinyHybrid + tinyShortDouble + 2 * product
           (* stage and cycle*)
           /\ (stage = "init" \/ stage = "extended")
           /\ stage' = "denatured"
           /\ UNCHANGED cycle

cool ==   /\ tee = "TooHot" \* when you just denatured
          /\ tee' = "Hot" \* cool off to "Hot"
          /\ stage = "denatured"
          /\ stage' = "ready"
          /\ UNCHANGED <<cycle, primer>>
          /\ UNCHANGED doubles
          /\ UNCHANGED templates
          /\ UNCHANGED hybrids

anneal ==   /\ tee = "Hot" \* too hot to anneal primers
            /\ tee' = "Warm" \* "Warm" is just right
            (* template/primer annealing *)
            /\ \E k \in 1..natMin(primer, sumList(templates)) : 
                /\ primer' = primer - k \* k consumed
                (* choose templates to anneal with primer *)
                /\ \E tup \in ((0..longTemplate) \X (0..shortTemplate) \X (0..tinyTemplate)):
                   /\ sumList(tup) = k
                   /\ longTemplate' = longTemplate - tup[1]
                   /\ longHybrid' = longHybrid + tup[1]
                   /\ shortTemplate' = shortTemplate - tup[2]
                   /\ shortHybrid' = shortHybrid + tup[2]
                   /\ tinyTemplate' = tinyTemplate - tup[3]
                   /\ tinyHybrid' = tinyHybrid + tup[3] 
            /\ stage = "ready"
            /\ stage' = "annealed"
            /\ UNCHANGED cycle \* dna can reanneal; we neglect that
            /\ UNCHANGED doubles            

extend ==   /\ tee = "Warm" \* too cool for extension
            /\ tee' = "Hot" \* "Hot" is just right
            (* any not annealed remained *)
            /\ UNCHANGED primer
            /\ UNCHANGED templates
            (* update doubles *)
            /\ UNCHANGED longLongDouble
            /\ shortLongDouble' = shortLongDouble + longHybrid
            /\ tinyShortDouble' = tinyShortDouble + shortHybrid
            /\ product' = product + tinyHybrid \* the only place you get hybrid from
            (* hybrids consumed *)
            /\ longHybrid' = 0
            /\ shortHybrid' = 0
            /\ tinyHybrid' = 0
            (* stage and cycle *)
            /\ stage = "annealed"
            /\ stage' = "extended"
            /\ cycle' = cycle + 1 \* only place this changes
            
(* initial state *)
Init == /\ tee = "Hot" \* not really all that hot
        /\ primer = PRIMER \* we have consumed no primers
        /\ longLongDouble = DNA \* subtle but important change
        (* and single-stranded templates *)
        /\ longTemplate = 0
        /\  shortTemplate = 0
        /\  tinyTemplate = 0
        (* and the hybrids *)
        /\  longHybrid = 0
        /\  shortHybrid = 0
        /\  tinyHybrid = 0          
        (* other doubles *)
        /\  shortLongDouble = 0
        /\  tinyShortDouble = 0                    
        /\  product = 0
        (* stage & cycle *)
        /\ stage = "init"
        /\ cycle = 0 \* no cycles completed
            
(* gathering up actions *)
Next == \/ heat
        \/ cool
        \/ anneal
        \/ extend

(* system spec *)
Spec == /\ Init 
        /\ [][Next]_vars 
        /\ WF_vars(anneal) 
        /\ WF_vars(heat)
        /\ WF_vars(cool)
        /\ WF_vars(extend)

(* type invariant *)
TypeOK == 
    /\ tee \in {"Warm", "Hot", "TooHot"}
    /\ primer \in Nat
    /\ stage \in {"init","ready","annealed","extended","denatured"}
    /\ cycle \in Nat
    /\ longTemplate \in Nat
    /\ shortTemplate \in Nat
    /\ tinyTemplate \in Nat
    /\ longHybrid \in Nat
    /\ shortHybrid \in Nat
    /\ tinyHybrid \in Nat
    /\ longLongDouble \in Nat
    /\ shortLongDouble \in Nat
    /\ tinyShortDouble \in Nat          
    /\ product \in Nat

(* safety *)
thirdCycleProduct == ((cycle < 3) => (product = 0))

(* refinement *)
stagesInstance == INSTANCE stages WITH
    template <- sumList(templates),
    hybrid <- sumList(hybrids),
    dna <- sumList(doubles)

stagesSpec == stagesInstance!Spec

primerDepleted == stagesInstance!primerDepleted

=============================================================================

