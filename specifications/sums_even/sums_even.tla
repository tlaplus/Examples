------------------------- MODULE sums_even -------------------------
\* A proof that the sum x+x of the natural number x is always even.  

EXTENDS Naturals, TLAPS

Even(x) == x % 2 = 0
Odd(x) == x % 2 = 1

\* Z3 can solve it in a single step
THEOREM \A x \in Nat : Even(x+x)
BY Z3 DEF Even

\* alternatively we prove this step-wise by making a case distinction on x being even or odd
THEOREM T1 == \A x \in Nat: Even(x+x)
<1>a TAKE x \in Nat
<1>1 \A z \in Nat : Even(z) \/ Odd(z) BY DEF Even, Odd
<1>2 CASE Even(x)
  <2> USE <1>2
  <2> ((x % 2) + (x % 2)) % 2 = (x+x)%2  BY <1>1 DEF Even, Odd
  <2> DEFINE A == x%2
  <2> HIDE DEF A
  <2> A = 0 => (A + A) % 2 = (0+0) %2 BY SMT DEF Even
  <2> QED BY DEF Even, A
<1>3 CASE Odd(x)
  <2> USE <1>3
  <2> ((x % 2) + (x % 2)) % 2 = (x+x)%2 BY <1>1 DEF Even, Odd
  <2> DEFINE A == x%2
  <2> HIDE DEF A
  <2> A = 1 => (A + A) % 2 = (1+1) %2 BY SMT DEF Even
  <2> QED BY DEF Even, Odd, A
<1> QED BY <1>1, <1>2, <1>3


=============================================================================
\* Modification History
\* Last modified Tue Mar 08 11:49:27 CET 2016 by marty
\* Created Mon Oct 26 15:01:26 CET 2015 by marty
