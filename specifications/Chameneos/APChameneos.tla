----------------------------- MODULE APChameneos -----------------------------
(* Apalache type annotations for Chameneos.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers

CONSTANT
  \* @type: Int;
  N,
  \* @type: Int;
  M

VARIABLE
  \* @type: Int -> <<Str, Int>>;
  chameneoses,
  \* @type: Int;
  meetingPlace,
  \* @type: Int;
  numMeetings

\* `Sum` is redefined here solely to attach a type annotation that constrains
\* the operator to `Int`. In TLA+ the original definition works for any value
\* whose `+` is defined (e.g. reals, sequences via concatenation in analogous
\* folds), but Apalache requires a concrete, monomorphic type.
\*
\* Brittle: this trick relies on SANY tolerating a duplicate definition only
\* when the body is identical to the one in `Chameneos`. Any change to the
\* body below turns the warning into a hard "Multiple declarations" error.
RECURSIVE Sum(_, _)
\* @type: (Int -> Int, Set(Int)) => Int;
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

INSTANCE Chameneos

==============================================================================
