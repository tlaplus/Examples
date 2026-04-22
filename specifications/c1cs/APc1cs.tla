------------------------------- MODULE APc1cs -------------------------------
(* Apalache type annotations for c1cs.tla, applied via INSTANCE so the
   original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS Integers, FiniteSets, TLC

CONSTANT
  \* @type: Int;
  N,
  \* @type: Int;
  F,
  \* @type: Int;
  T,
  \* @type: Set(VALUE);
  Values,
  \* @type: VALUE;
  Bottom

VARIABLES
  \* @type: Int -> Str;
  pc,
  \* @type: Int -> VALUE;
  v,
  \* @type: Int -> VALUE;
  dValue,
  \* @type: Set({ type: Str, value: VALUE, sndr: Int });
  bcastMsg,
  \* @type: Int -> Set({ type: Str, value: VALUE, sndr: Int });
  rcvdMsg

\* The original spec uses an inline tuple in
\*   `Spec == Init /\ [][Next]_<< pc, v, dValue, bcastMsg, rcvdMsg >> /\ ...`
\* which Snowcat cannot disambiguate. Provide a typed witness that matches the
\* original `vars` operator.
\* @type: <<Int -> Str, Int -> VALUE, Int -> VALUE, Set({ type: Str, value: VALUE, sndr: Int }), Int -> Set({ type: Str, value: VALUE, sndr: Int })>>;
vars == << pc, v, dValue, bcastMsg, rcvdMsg >>

INSTANCE c1cs

\* Concrete values for the uninterpreted-type constants.  The .cfg file
\* substitutes them via `Values <- ValuesVal` etc., because TLC-style
\* `Values = {v1, v2}` assignments would tag the model values as `Str`
\* in Apalache (and `VALUE \neq Str`).
ValuesVal == { "v1_OF_VALUE", "v2_OF_VALUE" }
BottomVal == "bottom_OF_VALUE"

=============================================================================
