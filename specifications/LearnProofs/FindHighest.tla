---------------------------- MODULE FindHighest -----------------------------
(***************************************************************************)
(* Defines a very simple algorithm that finds the largest value in a       *)
(* sequence of Natural numbers. This was created as an exercise in finding *)
(* & proving type invariants, inductive invariants, and correctness.       *)
(***************************************************************************)

EXTENDS Sequences, Naturals, Integers, TLAPS

(****************************************************************************
--algorithm Highest {
  variables
    f \in Seq(Nat);
    h = -1;
    i = 1;
  define {
    max(a, b) == IF a >= b THEN a ELSE b
  } {
lb: while (i <= Len(f)) {
      h := max(h, f[i]);
      i := i + 1;
    }
  }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "31f24270" /\ chksum(tla) = "819802c6")
VARIABLES f, h, i, pc

(* define statement *)
max(a, b) == IF a >= b THEN a ELSE b


vars == << f, h, i, pc >>

Init == (* Global variables *)
        /\ f \in Seq(Nat)
        /\ h = -1
        /\ i = 1
        /\ pc = "lb"

lb == /\ pc = "lb"
      /\ IF i <= Len(f)
            THEN /\ h' = max(h, f[i])
                 /\ i' = i + 1
                 /\ pc' = "lb"
            ELSE /\ pc' = "Done"
                 /\ UNCHANGED << h, i >>
      /\ f' = f

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

\* The type invariant; the proof system likes knowing variables are in Nat.
\* It's a good idea to check these invariants with the model checker before
\* trying to prove them. To quote Leslie Lamport, it's very difficult to
\* prove something that isn't true!
TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1..(Len(f) + 1)
  /\ i \in Nat
  /\ h \in Nat \cup {-1}

\* It's useful to prove the type invariant first, so it can be used as an
\* assumption in further proofs to restrict variable values.
THEOREM TypeInvariantHolds == Spec => []TypeOK
\* To prove theorems like Spec => []Invariant, you have to:
\*  1. Prove Invariant holds in the initial state (usually trivial)
\*  2. Prove Invariant holds when variables are unchanged (usually trivial)
\*  3. Prove that assuming Invariant is true, a Next step implies Invariant'
\* The last one (inductive case) is usually quite difficult. It helps to
\* never forget you have an extremely powerful assumption: that Invariant is
\* true!
PROOF
  \* The base case
  <1>a. Init => TypeOK
    BY DEFS Init, TypeOK
  \* The stuttering case
  <1>b. TypeOK /\ UNCHANGED vars => TypeOK'
    BY DEFS TypeOK, vars
  \* The inductive case; usually requires breaking down Next into disjuncts
  <1>c. TypeOK /\ Next => TypeOK'
    <2>a. TypeOK /\ lb => TypeOK'
      \* SUFFICES steps transform P => Q goals into Q goals, while assuming P
      <3> SUFFICES  ASSUME TypeOK, lb
                    PROVE TypeOK'
          OBVIOUS
      \* Making this a non-named step expands TypeOK and lb definitions for
      \* all subsequent & recursive steps in this sub-proof, without requiring
      \* the step to explicitly use BY DEFS TypeOK, lb
      <3> USE DEFS TypeOK, lb
      <3>a. CASE i <= Len(f) BY DEF max
      <3>b. CASE ~(i <= Len(f))
        <4>a. UNCHANGED <<f, h, i>> BY <3>b
        <4> QED BY <3>b, <4>a DEF lb
      <3> QED BY <3>a, <3>b
    <2>b. TypeOK /\ Terminating => TypeOK'
      BY DEFS TypeOK, Terminating, vars
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec

\* The inductive invariant; writing these is an art. You want an invariant
\* that can be shown to be true in every state, and if it's true in all
\* states, it can be shown to imply algorithm correctness as a whole.
InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
PROOF
  <1>a. Init => InductiveInvariant
    BY DEFS Init, InductiveInvariant
  <1>b. InductiveInvariant /\ UNCHANGED vars => InductiveInvariant'
    BY DEFS InductiveInvariant, vars
  \* Here we introduce TypeOK and TypeOK' as powerful assumptions, since we
  \* have already proved that Spec => []TypeOK. Note that TypeOK is a
  \* separate assumption from TypeOK' - including both can be the difference
  \* between a proof being impossible or trivial!
  <1>c. InductiveInvariant /\ TypeOK /\ TypeOK' /\ Next => InductiveInvariant'
    <2>a. InductiveInvariant /\ Terminating => InductiveInvariant'
      BY DEFS InductiveInvariant, Terminating, vars
    <2>b. InductiveInvariant /\ TypeOK /\ TypeOK' /\ lb => InductiveInvariant'
      <3> SUFFICES  ASSUME InductiveInvariant, TypeOK, TypeOK', lb
                    PROVE InductiveInvariant'
          OBVIOUS
      <3> USE DEF TypeOK
      <3>a. CASE i <= Len(f)
        <4>a. f[i] <= h' BY <3>a DEFS lb, max
        <4>b. h <= h' BY <3>a DEFS lb, max
        <4>c. \A idx \in 1..i : f[idx] <= h'
          BY <4>a, <4>b DEF InductiveInvariant
        <4>d. i = i' - 1 BY <3>a DEF lb
        <4>e. UNCHANGED f
          BY DEF lb
        \* These steps are annotated to use the Zenon prover, which succeeds
        \* immediately; otherwise we have to wait for other solvers to have
        \* their turn and fail.
        <4>f. \A idx \in 1..(i' - 1) : f'[idx] <= h'
          BY Zenon, <4>c, <4>d, <4>e
        <4> QED
          BY Zenon, <4>f DEF InductiveInvariant
      <3>b. CASE ~(i <= Len(f))
        <4> UNCHANGED <<f, h, i>> BY <3>b DEF lb
        <4> QED BY DEF InductiveInvariant
      <3> QED BY <3>a, <3>b DEF lb
    <2> QED BY <2>a, <2>b DEF Next
  \* We need to note we made use of the type invariant theorem here
  <1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec

\* A small sub-theorem that relates our inductive invariant to correctness
DoneIndexValue == pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
PROOF
  <1>a. Init => DoneIndexValue
    BY DEF Init, DoneIndexValue
  <1>b. DoneIndexValue /\ UNCHANGED vars => DoneIndexValue'
    BY DEFS DoneIndexValue, vars
  <1>c. DoneIndexValue /\ TypeOK /\ Next => DoneIndexValue'
    <2>a. DoneIndexValue /\ Terminating => DoneIndexValue'
      BY DEFS DoneIndexValue, Terminating, vars
    <2>b. DoneIndexValue /\ TypeOK /\ lb => DoneIndexValue'
      <3> SUFFICES  ASSUME DoneIndexValue, TypeOK, lb
                    PROVE DoneIndexValue'
          OBVIOUS
      <3> USE DEFS DoneIndexValue, TypeOK, lb
      <3>a. CASE i <= Len(f)
        <4>a. pc' /= "Done" BY <3>a
        <4> QED BY <3>a, <4>a DEF lb
      <3>b. CASE ~(i <= Len(f))
        <4>b. i \in 1..(Len(f) + 1) BY DEF TypeOK
        <4>c. i = Len(f) + 1 BY <3>b, <4>b
        <4>d. UNCHANGED <<f, i>> BY <3>b
        <4>e. i' = Len(f') + 1 BY <4>c, <4>d
        <4>f. pc' = "Done" BY <3>b
        <4> QED BY <4>e, <4>f DEF DoneIndexValue
      <3> QED BY <3>a, <3>b DEF lb
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec

\* The main event! After the algorithm has terminated, the variable h must
\* have value greater than or equal to any element of the sequence.
Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

THEOREM IsCorrect == Spec => []Correctness
PROOF
  <1>a. Init => Correctness
    BY DEF Init, Correctness
  <1>b. Correctness /\ UNCHANGED vars => Correctness'
    BY DEF Correctness, vars
  <1>c. /\ Correctness
        /\ InductiveInvariant'
        /\ DoneIndexValue'
        /\ Next
        => Correctness'
    <2>a. Correctness /\ Terminating => Correctness'
      BY DEF Correctness, Terminating, vars
    <2>b.
        /\ Correctness
        /\ InductiveInvariant'
        /\ DoneIndexValue'
        /\ lb
        => Correctness'
      <3> SUFFICES ASSUME
            Correctness,
            InductiveInvariant',
            DoneIndexValue',
            lb
          PROVE
            Correctness'
          OBVIOUS
      <3>a. CASE i <= Len(f)
        <4>a. pc' /= "Done" BY <3>a DEF lb
        <4> QED BY <3>a, <4>a DEFS Correctness, lb
      <3>b. CASE ~(i <= Len(f))
        <4>a. pc' = "Done" BY <3>b DEF lb
        <4>b. i' = Len(f') + 1 BY <4>a DEF DoneIndexValue
        <4>c. DOMAIN f' = 1..Len(f') BY lb
        <4>d. DOMAIN f' = 1..(i' - 1) BY <4>b, <4>c
        <4>e. \A idx \in 1..(i' - 1) : f'[idx] <= h'
          BY DEF InductiveInvariant
        <4>f. \A idx \in DOMAIN f' : f'[idx] <= h'
          BY <4>d, <4>e
        <4> QED BY <4>f DEF Correctness
      <3> QED BY <3>a, <3>b, lb
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED
    BY
      <1>a, <1>b, <1>c,
      InductiveInvariantHolds, DoneIndexValueThm, PTL
    DEF Spec

=============================================================================

