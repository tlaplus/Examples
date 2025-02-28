----------------------------- MODULE Consensus ------------------------------ 
(***************************************************************************)
(* The consensus problem requires a set of processes to choose a single    *)
(* value.  This module specifies the problem by specifying exactly what    *)
(* the requirements are for choosing a value.                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, FiniteSetTheorems, TLAPS

(***************************************************************************)
(* We let the constant parameter Value be the set of all values that can   *)
(* be chosen.                                                              *)
(***************************************************************************)
CONSTANT Value  

(****************************************************************************
We now specify the safety property of consensus as a trivial algorithm
that describes the allowed behaviors of a consensus algorithm.  It uses
the variable `chosen' to represent the set of all chosen values.  The
algorithm is trivial; it allows only behaviors that contain a single
state-change in which the variable `chosen' is changed from its initial
value {} to the value {v} for an arbitrary value v in Value.  The
algorithm itself does not specify any fairness properties, so it also
allows a behavior in which `chosen' is not changed.  We could use a
translator option to have the translation include a fairness
requirement, but we don't bother because it is easy enough to add it by
hand to the safety specification that the translator produces.

A real specification of consensus would also include additional
variables and actions.  In particular, it would have Propose actions in
which clients propose values and Learn actions in which clients learn
what value has been chosen.  It would allow only a proposed value to be
chosen.  However, the interesting part of a consensus algorithm is the
choosing of a single value.  We therefore restrict our attention to
that aspect of consensus algorithms.  In practice, given the algorithm
for choosing a value, it is obvious how to implement the Propose and
Learn actions.

For convenience, we define the macro Choose() that describes the action
of changing the value of `chosen' from {} to {v}, for a
nondeterministically chosen v in the set Value.  (There is little
reason to encapsulate such a simple action in a macro; however our
other specs are easier to read when written with such macros, so we
start using them now.) The `when' statement can be executed only when
its condition, chosen = {}, is true.  Hence, at most one Choose()
action can be performed in any execution.  The `with' statement
executes its body for a nondeterministically chosen v in Value.
Execution of this statement is enabled only if Value is
non-empty--something we do not assume at this point because it is not
required for the safety part of consensus, which is satisfied if no
value is chosen.

We put the Choose() action inside a `while' statement that loops
forever.  Of course, only a single Choose() action can be executed.
The algorithm stops after executing a Choose() action.  Technically,
the algorithm deadlocks after executing a Choose() action because
control is at a statement whose execution is never enabled.  Formally,
termination is simply deadlock that we want to happen.  We could just
as well have omitted the `while' and let the algorithm terminate.
However, adding the `while' loop makes the TLA+ representation of the
algorithm a tiny bit simpler.

--algorithm Consensus {
  variable chosen = {}; 
  macro Choose() { when chosen = {};
                   with (v \in Value) { chosen := {v} } }
   { lbl: while (TRUE) { Choose() }
   }  
}

The PlusCal translator writes the TLA+ translation of this algorithm
below.  The formula Spec is the TLA+ specification described by the
algorithm's code.  For now, you should just understand its two
subformulas Init and Next.  Formula Init is the initial predicate and
describes all possible initial states of an execution.  Formula Next is
the next-state relation; it describes the possible state changes
(changes of the values of variables), where unprimed variables
represent their values in the old state and primed variables represent
their values in the new state.
*****************************************************************************)
\***** BEGIN TRANSLATION  
VARIABLE chosen

vars == << chosen >>

Init == (* Global variables *)
        /\ chosen = {}

Next == /\ chosen = {}
        /\ \E v \in Value:
             chosen' = {v}

Spec == Init /\ [][Next]_vars

\***** END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now prove the safety property that at most one value is chosen.  We  *)
(* first define the type-correctness invariant TypeOK, and then define Inv *)
(* to be the inductive invariant that asserts TypeOK and that the          *)
(* cardinality of the set `chosen' is at most 1.  We then prove that, in   *)
(* any behavior satisfying the safety specification Spec, the invariant    *)
(* Inv is true in all states.  This means that at most one value is chosen *)
(* in any behavior.                                                        *)
(***************************************************************************)
TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen) 

Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

(***************************************************************************)
(* We now prove that Inv is an invariant, meaning that it is true in every *)
(* state in every behavior.  Before trying to prove it, we should first    *)
(* use TLC to check that it is true.  It's hardly worth bothering to       *)
(* either check or prove the obvious fact that Inv is an invariant, but    *)
(* it's a nice tiny exercise.  Model checking is instantaneous when Value  *)
(* is set to any small finite set.                                         *)
(*                                                                         *)
(* To understand the following proof, you need to understand the formula   *)
(* `Spec', which equals                                                    *)
(*                                                                         *)
(*    Init /\ [][Next]_vars                                                *)
(*                                                                         *)
(* where vars is the tuple <<chosen, pc>> of all variables.  It is a       *)
(* temporal formula satisfied by a behavior iff the behavior starts in a   *)
(* state satisfying Init and such that each step (sequence of states)      *)
(* satisfies [Next]_vars, which equals                                     *)
(*                                                                         *)
(*   Next \/ (vars'=vars)                                                  *)
(*                                                                         *)
(* Thus, each step satisfies either Next (so it is a step allowed by the   *)
(* next-state relation) or it is a "stuttering step" that leaves all the   *)
(* variables unchanged.  The reason why a spec must allow stuttering steps *)
(* will become apparent when we prove that a consensus algorithm satisfies *)
(* this specification of consensus.                                        *)
(***************************************************************************)

(***************************************************************************)
(* The following lemma asserts that Inv is an inductive invariant of the   *)
(* next-state action Next.  It is the key step in proving that Inv is an   *)
(* invariant of (true in every behavior allowed by) specification Spec.    *)
(***************************************************************************)
LEMMA InductiveInvariance ==
           Inv /\ [Next]_vars => Inv'
<1>. SUFFICES ASSUME Inv, [Next]_vars
              PROVE  Inv'
  OBVIOUS
<1>1. CASE Next 
  \* In the following BY proof, <1>1 denotes the case assumption Next 
  BY <1>1, FS_EmptySet, FS_Singleton DEF Inv, TypeOK, Next
<1>2. CASE vars' = vars
  BY <1>2 DEF Inv, TypeOK, vars  
<1>3. QED
  BY <1>1, <1>2 DEF Next

THEOREM Invariance == Spec => []Inv 
<1>1.  Init => Inv
  BY FS_EmptySet DEF Init, Inv, TypeOK
<1>2.  QED
 BY PTL, <1>1, InductiveInvariance DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define LiveSpec to be the algorithm's specification with the     *)
(* added fairness condition of weak fairness of the next-state relation,   *)
(* which asserts that execution does not stop if some action is enabled.   *)
(* The temporal formula Success asserts that some value is chosen.         *)
(* Below, we prove that LiveSpec implies that Success holds eventually.    *)
(* This means that, in every behavior satisfying LiveSpec, some value will *)
(* be chosen.                                                              *)
(***************************************************************************)
LiveSpec == Spec /\ WF_vars(Next)
Success == <>(chosen # {})

(***************************************************************************)
(* For liveness, we need to assume that there exists at least one value.   *)
(***************************************************************************)
ASSUME ValueNonempty == Value # {}

(***************************************************************************)
(* Since fairness is defined in terms of the ENABLED operator, we must     *)
(* characterize states at which an action is enabled. It is usually a good *)
(* idea to prove a separate lemma for this.                                *)
(***************************************************************************)
LEMMA EnabledNext ==
    (ENABLED <<Next>>_vars) <=> (chosen = {})
BY ValueNonempty, ExpandENABLED DEF Next, vars

(***************************************************************************)
(* Here is our proof that Livespec implies Success. The overall approach   *)
(* to the proof follows the rule WF1 discussed in                          *)
(*                                                                         *)
(* `. AUTHOR  = "Leslie Lamport",                                          *)
(*    TITLE   = "The Temporal Logic of Actions",                           *)
(*    JOURNAL = toplas,                                                    *)
(*    volume  = 16,                                                        *)
(*    number  = 3,                                                         *)
(*    YEAR    = 1994,                                                      *)
(*    month   = may,                                                       *)
(*    PAGES   = "872--923"         .'                                      *)
(*                                                                         *)
(* In the actual proof, use of this rule is subsumed by appealing to the   *)
(* PTL decision procedure for propositional temporal logic. When reasoning *)
(* about the liveness of more complex specifications, an additional        *)
(* invariant would typically be required.                                  *)
(***************************************************************************)
THEOREM LiveSpec => Success
<1>1. [][Next]_vars /\ WF_vars(Next) => [](Init => Success)
  <2>1. Init' \/ (chosen # {})'
    BY DEF Init
  <2>2. Init /\ <<Next>>_vars => (chosen # {})'
    BY DEF Init, Next, vars
  <2>3. Init => ENABLED <<Next>>_vars
    BY EnabledNext DEF Init
  <2>. QED  BY <2>1, <2>2, <2>3, PTL DEF Success
<1>2. QED  BY <1>1, PTL DEF LiveSpec, Spec, Success

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following theorem is used in the refinement proof in module         *)
(* VoteProof.                                                              *)
(***************************************************************************)
THEOREM LiveSpecEquals ==
          LiveSpec <=> Spec /\ ([]<><<Next>>_vars \/ []<>(chosen # {}))
<1>1. (chosen # {}) <=> ~(chosen = {})
  OBVIOUS
<1>2. ([]<>~ENABLED <<Next>>_vars) <=> []<>(chosen # {})
  BY <1>1, EnabledNext, PTL
<1>4. QED
  BY <1>2, PTL DEF LiveSpec
=============================================================================
\* Modification History
\* Last modified Mon May 11 18:36:27 CEST 2020 by merz
\* Last modified Mon Aug 18 15:00:45 CEST 2014 by tomer
\* Last modified Mon Aug 18 14:58:57 CEST 2014 by tomer
\* Last modified Tue Feb 14 13:35:49 PST 2012 by lamport
\* Last modified Mon Feb 07 14:46:59 PST 2011 by lamport
