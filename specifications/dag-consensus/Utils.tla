------------- MODULE Utils ---------------

EXTENDS Integers

Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

==========================================
