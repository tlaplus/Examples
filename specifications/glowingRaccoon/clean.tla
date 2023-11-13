----------------------------- MODULE clean -----------------------------

\* PCR amplifies a desired snippet of DNA.
\* This is the basic picture of PCR:
\* High heat denatures DNA, producing single-stranded templates. 
\* Lower heat allows annealing of primers to sites on templates.
\* (Primers are carefully chosen for this purpose.)
\* Hybrids are produced by annealing at this lower temperature.
\* Polymerase attaches to hybrids and extends them to new DNA.
\* Extension occurs at medium heat, between annealing and denaturing. 
\* The whole cycle repeats, yield S-curve growth of the product.
\* The goal is to produce more DNA, but just any DNA? No!
\* See refinements in "stages.tla" and "product.tla".

\* Many factors contribute to successful PCR.
\* Most of them are neglected here.
\* In particular, nucleotides are just assumed to be there.
\* Two different types of primer are required.
\* (our spec allows for this; further refinement could distinguish)
\* Extension is assumed to happen to available hybrids.
\* Temporal Logic of Actions is not the perfect tool for this!
\* Hopefully, the exercise is worthwhile.

EXTENDS Naturals \* an import - copies module in there

CONSTANTS DNA, PRIMER \* starting stock of key things

VARIABLES tee, \* temperature, a string
          primer, \* count of primers remaining
          dna, \* count of double strands present
          template, \* count of single strands present
          hybrid \* count of template-primer hybrids

(* list of state variables, for convenience *)
vars == << tee, primer, dna, template, hybrid >>
          
(* helper function *)
natMin(i,j) == IF i < j THEN i ELSE j \* min of two nats

(* actions *)
heat == /\ tee = "Hot" \* current temperature is "Hot"
        /\ tee' = "TooHot" \* heat up to "TooHot"
        /\ primer' = primer + hybrid \* we'll take those back, thanks
        /\ dna' = 0 \* the dna denatures
        /\ template' = template + hybrid + 2 * dna \* has to go somewhere
        /\ hybrid' = 0 \* these denature too

cool == /\ tee = "TooHot" \* when you just denatured
        /\ tee' = "Hot" \* cool off to "Hot"
        /\ UNCHANGED << primer, dna, template, hybrid >>

anneal == /\ tee = "Hot" \* too hot to anneal primers
          /\ tee' = "Warm" \* "Warm" is just right
          /\ UNCHANGED dna \* dna can reanneal; we neglect that
          (* this is the neat part *)
          /\ \E k \in 1..natMin(primer, template) : 
             /\ primer' = primer - k \* k consumed
             /\ template' = template - k \* k consumed
             /\ hybrid' = hybrid + k \* k more hybrids

extend == /\ tee = "Warm" \* too cool for extension
            /\ tee' = "Hot" \* "Hot" is just right
            /\ UNCHANGED <<primer, template>>
            /\ dna' = dna + hybrid \* assuming it just happens
            /\ hybrid' = 0 \* all turned to dna
            
(* initial state *)
Init == /\ tee = "Hot" \* not really all that hot
        /\ primer = PRIMER \* we have consumed no primers
        /\ dna = DNA \* we start with some nice 'frozen' dna
        /\ template = 0 \* everything is bound up
        /\ hybrid = 0 \* no annealing has happened yet
            
(* state transition *)
Next ==  \/ heat
         \/ cool
         \/ anneal
         \/ extend

(* specification of system *)
Spec == /\ Init 
        /\ [][Next]_vars 

(* type invariant *)
TypeOK == 
    /\ tee \in {"Warm", "Hot", "TooHot"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

(* safety *)
primerPositive == (primer >= 0) \* a redundant invariant

(* preservation as an invariant *)
preservationInvariant == template + primer + 2*(dna + hybrid) = PRIMER + 2 * DNA

(* preservation as a property *)
constantCount == UNCHANGED ( template + primer + 2*(dna + hybrid) )
preservationProperty == [][constantCount]_vars \* as property

(* liveness *)
primerDepleted == <>(primer = 0) \* does not hold!

=============================================================================
