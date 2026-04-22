-------------------------- MODULE APReadersWriters --------------------------
(* Apalache type annotations for ReadersWriters.tla, applied via INSTANCE so
   the original spec remains free of tool-specific idiosyncrasies. *)

EXTENDS FiniteSets, Naturals, Sequences

CONSTANT
  \* @type: Int;
  NumActors

VARIABLES
  \* @type: Set(Int);
  readers,
  \* @type: Set(Int);
  writers,
  \* @type: Seq(<<Str, Int>>);
  waiting

\* The helpers `ToSet`, `read` and `write` are redefined here solely to attach
\* type annotations that constrain them to the concrete shape used by this
\* spec (sequences of `<<Str, Int>>`). In plain TLA+ the original definitions
\* are polymorphic and work for any sequence / tuple where the indexing makes
\* sense, but Apalache requires a concrete, monomorphic type.
\*
\* Brittle: this trick relies on SANY tolerating a duplicate definition only
\* when the body is identical to the one in `ReadersWriters`. Any change to
\* the bodies below turns the warning into a hard "Multiple declarations"
\* error.
\* @type: Seq(<<Str, Int>>) => Set(<<Str, Int>>);
ToSet(s) == { s[i] : i \in DOMAIN s }

\* @type: <<Str, Int>> => Bool;
read(s) == s[1] = "read"
\* @type: <<Str, Int>> => Bool;
write(s) == s[1] = "write"

INSTANCE ReadersWriters

==============================================================================
