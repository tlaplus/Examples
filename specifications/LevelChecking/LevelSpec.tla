 ----------------------------- MODULE LevelSpec ------------------------------
 (***************************************************************************)
 (* This module specifies the level-checking for the TLA+ language.  See    *)
 (* Section 17.2 of "Specifying Systems" for a discussion of levels and     *)
 (* level checking in TLA+.                                                 *)
 (*                                                                         *)
 (* The semantics of TLA+ requires that, in the following constructs, e     *)
 (* must have level at most 1 (that is, not contain primed variables) and   *)
 (* A and B must have level at most 2 (that is, not contain temporal        *)
 (* operators):                                                             *)
 (*                                                                         *)
 (*    e'    [A]_e    <<A>>_e    ENABLED A    UNCHANGED e    A \cdot B      *)
 (*                                                                         *)
 (* Although the semantics doesn't really demand it, we also use level      *)
 (* checking to rule out some bizarre expressions like                      *)
 (*                                                                         *)
 (*    []F + []G                                                            *)
 (*                                                                         *)
 (* We do this by requiring that an operator argument that can normally be  *)
 (* a non-Boolean must have level at most 2, so it cannot be a temporal     *)
 (* formula.  Thus, in the expression                                       *)
 (*                                                                         *)
 (*    {e, f}                                                               *)
 (*                                                                         *)
 (* we require that e and f have level at most 2.                           *)
 (*                                                                         *)
 (* There is another aspect of level checking that is not described here.   *)
 (* TLA (as opposed to "raw TLA") does not allow an action like x'=x+1 to   *)
 (* be used as a temporal formula.  Thus, in all the following formulas, F  *)
 (* and G can have any level other than 2:                                  *)
 (*                                                                         *)
 (*    []F    <<F>>    F ~> G    F -+-> G    \EE x : F    \AA x : F         *)
 (*                                                                         *)
 (* A general algorithm for detecting all violations of this requirement    *)
 (* is nontrivial.  For example, if we have                                 *)
 (*                                                                         *)
 (*      ----- MODULE M -----                                               *)
 (*      CONSTANTS A, Op(_)                                                 *)
 (*      B == Op(A)                                                         *)
 (*      ====================                                               *)
 (*                                                                         *)
 (*      ------------- MODULE I -------------                               *)
 (*      VARIABLE x                                                         *)
 (*      C(F) == []F                                                        *)
 (*      INSTANCE M WITH A <- x'=x+1, Op <- C                               *)
 (*      ====================================                               *)
 (*                                                                         *)
 (* then the last instance is illegal because it defines B in module I to   *)
 (* equal the illegal formula [](x'=x+1).  Again, this specification does   *)
 (* not handle this problem.  I presume that the initial version of SANY    *)
 (* will do a simple check of the level of an expression F or G in the      *)
 (* expressions listed above, and complain only if the expression has       *)
 (* explicit level 2.                                                       *)
 (***************************************************************************)

 EXTENDS Integers, Sequences
 -----------------------------------------------------------------------------
                         (****************************)
                         (* Some Useful Definitions  *)
                         (****************************)
 NumMax(i, j) == IF i > j THEN i ELSE j
 \* Max is apparently defined in the TLC overridden Naturals module
   (*************************************************************************)
   (* The maximum of the number i and j.                                    *)
   (*************************************************************************)

 SetMax(S) ==  IF S = {} THEN 0
                         ELSE CHOOSE x \in S : \A y \in S : x \geq y
   (*************************************************************************)
   (* The maximum of the set S of natural numbers.                          *)
   (*************************************************************************)

 RecordCombine(S, T) ==
   (*************************************************************************)
   (* If S and T are sets of records, then this equals the set of all       *)
   (* records rc(s,t) with s in S and t in T, where rc(s,t) is the record   *)
   (* obtained by "merging" s and t--that is, forming the record whose set  *)
   (* of fields is the union of the sets of fields of the two records.      *)
   (*************************************************************************)
   LET rc(s, t) ==
        [i \in (DOMAIN s) \cup (DOMAIN t) |-> IF i \in DOMAIN s THEN s[i]
                                                                ELSE t[i]]
   IN  {rc(s, t) : s \in S, t \in T}
 -----------------------------------------------------------------------------
 CONSTANT  NodeId, Node
   (*************************************************************************)
   (* We represent a collection of TLA+ modules by a semantic forest,       *)
   (* composed of nodes that may contain references to other nodes.  Each   *)
   (* module is represented by a tree that may have links to the nodes of   *)
   (* other modules that it imports.  The set NodeId is the set of all node *)
   (* identifiers, which can be thought of as the set of references to      *)
   (* nodes.  The constant Node is a function from NodeId to the set (type) *)
   (* of all possible semantic nodes.                                       *)
   (*************************************************************************)

 Null == CHOOSE n : n \notin NodeId
   (*************************************************************************)
   (* A value that is not a node id.                                        *)
   (*************************************************************************)
 -----------------------------------------------------------------------------
 (***************************************************************************)
 (*                            The Semantic Nodes                           *)
 (*                            ------------------                           *)
 (* Here are the kinds of semantic nodes and what they represent            *)
 (*                                                                         *)
 (*    ModuleNode        : A module                                         *)
 (*    InstanceNode      : An INSTANCE statement                            *)
 (*    OpDefNode         : An operator definition.  As explained            *)
 (*                        below, all built-in TLA+ constructs are          *)
 (*                        represented as defined operators.                *)
 (*    ConstantDeclNode  : A constant declaration or a formal parameter     *)
 (*                          of a definition                                *)
 (*    VariableDeclNode  : A variable declaration.                          *)
 (*    OpDeclNode        : A ConstantDeclNode or a VariableDeclNode         *)
 (*    OpApplNode        : An application of an operator.                   *)
 (*    SubstitutionNode  : The sequence of WITH substitutions for an        *)
 (*                        INSTANCE statement.                              *)
 (*    BoundSymbolNode   : A bounded identifier.                            *)
 (*    LetInNode         : A LET/IN statement.                              *)
 (*    ValueNode         : A string or number.                              *)
 (*    IdentifierNode    : An expression consisting of a single symbol.     *)
 (*                        Also used to represent an operator argument of   *)
 (*                        a second-order operator.                         *)
 (*    OpDefOrDeclNode   : An OpDefNode or an OpDeclNode.                   *)
 (*    ExprNode          : An expression, which is an OppApplNode, a        *)
 (*                        LetInNode, a ValueNode, an IdentifierNode,       *)
 (*                                                                         *)
 (* Note: The SANY API apparently includes the following object types and   *)
 (* kinds not included as semantic nodes in this spec.  Here is what they   *)
 (* correspond to in this spec:                                             *)
 (*                                                                         *)
 (*    FormalParamNode object : Represented by a ConstantDeclNode.          *)
 (*                                                                         *)
 (*    OpArgNode object : Represented by an IdentifierNode.                 *)
 (*                                                                         *)
 (* For every kind xxxNode of semantic node, we define xxxNodeId to be the  *)
 (* set of node ids of nodes of kind xxxNode.  We use the fact that a       *)
 (* semantic node has a kind field and an xxxNode object has kind field     *)
 (* equal to "xxxNode".                                                     *)
 (***************************************************************************)
 Ref(str) == {id \in NodeId : Node[id].kind = str}

 ModuleNodeId        == Ref("ModuleNode")
 InstanceNodeId      == Ref("InstanceNodeId")
 OpDefNodeId         == Ref("OpDefNode")
 ConstantDeclNodeId  == Ref("ConstantDeclNode")
 VariableDeclNodeId  == Ref("VariableDeclNode")
 OpDeclNodeId        == ConstantDeclNodeId \cup VariableDeclNodeId
 OpApplNodeId        == Ref("OpApplNode")
 SubstitutionNodeId  == Ref("SubstitutionNode")
 BoundSymbolNodeId   == Ref("BoundSymbolNode")
 LetInNodeId         == Ref("LetInNode")
 ValueNodeId         == Ref("ValueNode")
 IdentifierNodeId    == Ref("IdentifierNode")
 OpDefOrDeclNodeId   == OpDefNodeId \cup OpDeclNodeId
 ExprNodeId          == OpApplNodeId \cup LetInNodeId  \cup ValueNodeId
                          \cup IdentifierNodeId
 -----------------------------------------------------------------------------
                      (**************************)
                      (* Level Data Structures  *)
                      (**************************)

 LevelValue == 0..3
   (*************************************************************************)
   (* The set of levels, where                                              *)
   (*    0 = constant                                                       *)
   (*    1 = state function                                                 *)
   (*    2 = action                                                         *)
   (*    3 = temporal formula                                               *)
   (* (See Section 17.2 of "Specifying Systems".)                           *)
   (*************************************************************************)

 (***************************************************************************)
 (* To understand level checking, consider the following definition.        *)
 (*                                                                         *)
 (*    Foo(a, b, c) == a /\ ENABLED(b'=c)                                   *)
 (*                                                                         *)
 (* Since a level-2 expression cannot be primed and the argument of ENABLED *)
 (* can have level at most 2, an expression Foo(exp1, exp2, exp3) is legal  *)
 (* iff the level of exp2 is at most 1 and the level of exp3 is at most 2.  *)
 (* An ENABLED expression has level equal to 1.  (For simplicity, we        *)
 (* consider ENABLED (1=1), which is equivalent to TRUE, to have level 1.)  *)
 (* Hence, the expression Foo(exp1, exp2, exp3) has level equal to the      *)
 (* maximum of 1 and the level of a.                                        *)
 (*                                                                         *)
 (* We can describe the level properties of the operator Foo as follows,    *)
 (* where n is the semantic OpDefNode corresponding to the definition of    *)
 (* Foo.  We define the level constraints on the arguments of Foo by        *)
 (* n.maxLevels, where n.maxLevels[i] is the maximum level of the i-th      *)
 (* argument of Foo.  Thus,                                                 *)
 (*                                                                         *)
 (*    n.maxLevels[1] = 3                                                   *)
 (*    n.maxLevels[2] = 1                                                   *)
 (*    n.maxLevels[3] = 2                                                   *)
 (*                                                                         *)
 (* The level of Foo(exp1, exp2, exp3) is the maximum of 1 and the level of *)
 (* exp1.  We can express that by saying that it is the maximum of 1 and    *)
 (* the maximum of the set                                                  *)
 (*                                                                         *)
 (*   {1 * level of exp1, 0 * level of exp2, 0 * level of exp3}             *)
 (*                                                                         *)
 (* The level of an application of Foo is described by                      *)
 (*                                                                         *)
 (*   n.level = 1                                                           *)
 (*   n.weights[1] = 1                                                      *)
 (*   n.weights[2] = 0                                                      *)
 (*   n.weights[3] = 0                                                      *)
 (*                                                                         *)
 (* This is all simple enough.  Things get complicated for 2nd-order        *)
 (* operators, which are operators that take an operator as an              *)
 (* argument--for example                                                   *)
 (*                                                                         *)
 (*   Op2(A(_,_,_), b, c) == A(b, x', c)                                    *)
 (*                                                                         *)
 (* The expression Op2(Foo, exp2, exp3) is illegal, because it expands to   *)
 (*                                                                         *)
 (*    Foo(exp2, x', exp3)                                                  *)
 (*                                                                         *)
 (* and the second of argument of Foo can have level at most 1.  In other   *)
 (* words, we cannot substitute Foo for the first argument of Op2 because   *)
 (* Foo.maxLevels[2] = 1 and the first argument of Op2 must be able to take *)
 (* a second argument of level 2.  In general, for an OpDefNode op          *)
 (* representing a definition of an operator Op, we let                     *)
 (* op.minMaxLevel[i][k] be the minimum value of oparg.maxLevels[k] for the *)
 (* i-th argument of Op.  Thus, op.minMaxLevels[i] is a sequenced whose     *)
 (* length is the number of arguments taken by the i-th argument of Op.     *)
 (* (It equals 0 if the i-th argument of Op is not an operator argument.)   *)
 (*                                                                         *)
 (* An ideal level-checking algorithm would have the property that it       *)
 (* considers an expression to be level-correct iff expanding all defined   *)
 (* operators to obtain an expression that contains only built-in operators *)
 (* yields a level-correct expression.  The following example indicates the *)
 (* complexity of an ideal algorithm that doesn't actually do the           *)
 (* expansion.                                                              *)
 (*                                                                         *)
 (*    Bar(Op1(_,_)) == Op1(x', x)'                                         *)
 (*                                                                         *)
 (* The expression Bar(A) is level-correct iff A is an operator whose level *)
 (* does not depend on the level of its first argument--that is, iff        *)
 (* a.weight[1]=0.  To simplify the bookkeeping, we make the conservative   *)
 (* assumption that any operator parameter may be instantiated with an      *)
 (* operator whose level depends on the levels of all its arguments.  Thus, *)
 (* we will disallow this definition of Bar.  We will do this even if the   *)
 (* definition occurs within a LET and we could check that all the actual   *)
 (* instances of Bar result in level-correct expressions.  I can't think of *)
 (* any reasonable case where this will disallow a level-correct expression *)
 (* that a user is likely to write.                                         *)
 (*                                                                         *)
 (* The decision to simplify the bookkeeping results in the following,      *)
 (* somewhat less unlikely problem.  With the definitions                   *)
 (*                                                                         *)
 (*    ApplyToPrime(Op(_)) == Op(x')                                        *)
 (*    EqualsNoPrime(a) == x                                                *)
 (*                                                                         *)
 (* the expression  ApplyToPrime(EqualsNoPrime)' , which equals x', is      *)
 (* considered to be illegal.  This is because the algorithm to compute the *)
 (* level makes the assumption that ApplyToPrime will always be applied to  *)
 (* operators Op for which the level of Op(exp) depends on the level of     *)
 (* exp.  Hence, SANY's algorithm gives ApplyToPrime(Op) a level of at      *)
 (* least 2 (primed expression) for any operator Op.  A slightly more       *)
 (* realistic example can be constructed by modifying ApplyToPrime a bit    *)
 (* and applying it to ENABLED.                                             *)
 (* TLC warns users about this bug if it reports an invariant to be         *)
 (* level-incorrect in tlc2.tool.Spec.processConfigInvariants() with error  *)
 (* code tlc2.output.EC.TLC_INVARIANT_VIOLATED_LEVEL.                       *)
 (* A corresponding test can be found in test52. Its invariant "Invariant"  *)
 (* covers the ENABLED scenario. However, the invariant remains disabled    *)
 (* for as long as this bug is open. The invariant Invariant can be         *)
 (* re-enabled in test52.cfg once this bug is closed.                       *)
 (*                                                                         *)
 (* To compute the values of op.level, op.weights, and op.minMaxLevel for   *)
 (* an OpDefNode op corresponding to a definition, a level-checking         *)
 (* algorithm needs to keep track of the constraints on its formal          *)
 (* parameters implied by the subexpressions of the definition's body, as   *)
 (* well has how the level of the body depends on the levels of its         *)
 (* parameters.  For our less than ideal level-checking algorithm, this is  *)
 (* done by keeping track of sets of objects of the following types.        *)
 (***************************************************************************)

 LevelConstraint == [param : ConstantDeclNodeId, level : LevelValue]
   (*************************************************************************)
   (* A level constraint lc indicates that the parameter with id lc.param   *)
   (* can be instantiated only with an expression of level at most          *)
   (* lc.level.                                                             *)
   (*************************************************************************)

 ArgLevelConstraint ==
   (*************************************************************************)
   (* An arg-level constraint alc indicates that the operator parameter     *)
   (* with id alc.param can be instantiated with an operator op only if the *)
   (* alc.idx-th argument of op can have level at least alc.level.  This    *)
   (* constraint is vacuous iff alc.level = 0.                              *)
   (*************************************************************************)
   [param : ConstantDeclNodeId,  idx : Nat \ {0},  level : LevelValue]

 ArgLevelParam ==
   (*************************************************************************)
   (* An arg-level parameter alp indicates that the parameter with id       *)
   (* alp.param appears in the alp.idx-th argument of the operator with id  *)
   (* alp.op.                                                               *)
   (*************************************************************************)
   [op : NodeId, idx : Nat \ {0}, param : NodeId]


 (***************************************************************************)
 (* For later use, we define the following two operators on these data      *)
 (* types.                                                                  *)
 (***************************************************************************)

 MinLevelConstraint(id, LC) ==
   (*************************************************************************)
   (* If LC is a set of level constraints and id a ConstantDeclNodeId, then *)
   (* this equals the minimum level constraint on id implied by the         *)
   (* elements of LC. (This is 3 if there is none.)                         *)
   (*************************************************************************)
   IF \E lc \in LC : lc.param = id
     THEN LET minLC == CHOOSE lc \in LC :
                         /\ lc.param = id
                         /\ \A olc \in LC :
                              (olc.param = id) => (olc.level \geq lc.level)
          IN  minLC.level
     ELSE 3

 MaxArgLevelConstraints(id, ALC) ==
   (*************************************************************************)
   (* If ALC is a set of arg-level constraints and id a ConstantDeclNodeId, *)
   (* then this equals the tuple <<lev_1, ..., lev_n>>, where n is the      *)
   (* number of arguments taken by the operator parameter op represented by *)
   (* node id, such that the arg-level constraints in ALC imply that op     *)
   (* must be able to take an i-th operator of level at least lev_i, for    *)
   (* each i.                                                               *)
   (*************************************************************************)
   LET n == Node[id].numberOfArgs
       minALC(i) ==
         LET isALC(lc) == (lc.param = id) /\ (lc.idx = i)
         IN  IF \E lc \in ALC : isALC(lc)
               THEN LET max == CHOOSE lc \in ALC :
                                 /\ isALC(lc)
                                 /\ \A olc \in ALC :
                                      isALC(olc) => (olc.level \leq lc.level)
                    IN  max.level
               ELSE 0
   IN [i \in 1..n |-> minALC(i)]

 LevelConstraintFields ==
   (*************************************************************************)
   (* A record whose fields consist of fields used for level computations.  *)
   (* These fields are common to all semantic nodes of type Expr that       *)
   (* represent expressions, as well as to all OpDef nodes, which represent *)
   (* operator definitions.  Some of these fields also occur in other       *)
   (* nodes--like Instance and Module nodes.                                *)
   (*                                                                       *)
   (* In general, an expression will be in the scope of some formal         *)
   (* parameters, so its level will depend on the level of the expressions  *)
   (* substituted for some of those parameters.  For example, if p and q    *)
   (* are formal parameters, and x is a declared variable, then the level   *)
   (* of the expression                                                     *)
   (*                                                                       *)
   (*    ENABLED(p' = x) /\ q                                               *)
   (*                                                                       *)
   (* is the maximum of 1 (the level of the ENABLED expression) and the     *)
   (* level of q.  For the ExprNode e that represents this expression,      *)
   (* e.level equals 1 and e.levelParams is the set whose single element is *)
   (* the (id of the) ConstantDeclNode for q.  Here's a description         *)
   (* of the level fields, where the parameter set of e is the set of all   *)
   (* parameters (formal definition parameters or declared constants) such  *)
   (* that e appears in the scope of their declarations.                    *)
   (*                                                                       *)
   (*   e.level:  A level value.  If all the parameters appearing in e      *)
   (*      were instantiated with constants, then e.level would be          *)
   (*      the level of the resulting expression.                           *)
   (*                                                                       *)
   (*   e.levelParams : A set of parameters from the parameter set of e.    *)
   (*       You can think of these in two equivalent ways:                  *)
   (*        - They are the parameters whose levels contribute to the       *)
   (*          level of e.                                                  *)
   (*        - They are the parameters appearing in e that would get        *)
   (*          primed  if expression e were primed.                         *)
   (*       An element of e.levelParams is called a LEVEL PARAMETER of e.   *)
   (*                                                                       *)
   (*   e.levelConstraints : A set of level constraints, in which           *)
   (*       all the parameters that appear belong to the parameter set      *)
   (*       of e.                                                           *)
   (*                                                                       *)
   (*   e.argLevelConstraints : A set of arg-level constraints, in which    *)
   (*       all the parameters that appear are (operator) parameters of     *)
   (*       the parameter set of e.                                         *)
   (*                                                                       *)
   (*   e.argLevelParams : A set of arg-level parameters.                   *)
   (*       An element alp indicates that there is a subexpression of e     *)
   (*       (or of its definition, if e is a defined operator)              *)
   (*       of the form alp.op(... ), where alp.param is a                  *)
   (*       level parameter of the alp.idx-th argument.                     *)
   (*       NOTE: For an OpDefNode op, op.argLevelParams can contain        *)
   (*       elements alp with alp.op and/or alp.param (but not both)        *)
   (*       being formal parameters of the definition.  This will           *)
   (*       happen if the definition contains a subexpression Op(arg)       *)
   (*       where either Op is a formal parameter or arg contains a         *)
   (*       formal parameter.  (These elements are used for level-checking  *)
   (*       an instantiated version of the definition obtained by an        *)
   (*       INSTANCE statement.)                                            *)
   (*                                                                       *)
   (* In the computation, we don't bother eliminating redundant elements    *)
   (* from these sets.  For example, a level constraint lc is redundant if  *)
   (* there is another level constraint lco such that lco.param = lc.param  *)
   (* and lco.level < lc.level.  A more efficient algorithm would eliminate *)
   (* the redundant elements from e.levelConstraints and                    *)
   (* e.argLevelConstraints.                                                *)
   (*************************************************************************)
   [levelParams         : SUBSET ConstantDeclNodeId,
    levelConstraints    : SUBSET LevelConstraint,
    argLevelConstraints : SUBSET ArgLevelConstraint,
    argLevelParams      : SUBSET ArgLevelParam]
 -----------------------------------------------------------------------------
 (***************************************************************************)
 (*                   Definitions of the Semantic Nodes                     *)
 (*                                                                         *)
 (* A fair amount of information not relevant to level checking, but        *)
 (* present in the SANY api, has been eliminated from these definitions of  *)
 (* the semantic node types.  For example, some sequences have been changed *)
 (* to sets where their order of occurrence is not relevant to level        *)
 (* checking (but is relevant to correctness of the module).                *)
 (***************************************************************************)

 ModuleNode ==
   (*************************************************************************)
   (* A semantic node representing a module.                                *)
   (*************************************************************************)
   [kind : {"ModuleNode"},
    isConstant : BOOLEAN,
      (**********************************************************************)
      (* True iff this is a constant module.  A constant module is one with *)
      (* no VARIABLE declarations and no non-constant operators.  We won't  *)
      (* bother defining this precisely.                                    *)
      (*                                                                    *)
      (* Note: In TLA+, the only way to define a constant operator that     *)
      (* contains a non-constant subexpression is by throwing the           *)
      (* subexpression away--for example:                                   *)
      (*                                                                    *)
      (*      Foo(a) == LET Bar(b, c) == b                                  *)
      (*                IN  Bar(a, x')                                      *)
      (*                                                                    *)
      (* which is a silly way to write Foo(a) == a.  It would thus be safe  *)
      (* to define a constant module to be one with no declared variables   *)
      (* and in which all definitions and theorems have level 0.  This      *)
      (* would allow a constant module to have the silly definition above   *)
      (* of Foo (assuming x is not a declared variable).  However, the      *)
      (* official definition of a constant module prohibits it from having  *)
      (* definitions like the one above for Foo.                            *)
      (**********************************************************************)
    opDecls : SUBSET OpDeclNodeId,
      (**********************************************************************)
      (* The set declared constants and variables.                          *)
      (**********************************************************************)
    opDefs  : SUBSET OpDefNodeId,
     (***********************************************************************)
     (* The top-level operator definitions (ones not defined inside LET's)  *)
     (* in this module--including definitions incorporated from extended    *)
     (* and instantiated modules.  It includes function definitions         *)
     (* (definitions of the form f[x \in S] == e) and all definitions       *)
     (* introduced into the module by module instantiations.  (A module     *)
     (* instantiation creates a new OpDefNode for each OpDefNode in the     *)
     (* instantiated module.)                                               *)
     (***********************************************************************)
    instances : SUBSET InstanceNodeId,
      (**********************************************************************)
      (* The top-level INSTANCEs (ones not defined inside LET's) in this    *)
      (* module.                                                            *)
      (**********************************************************************)
    innerModules : SUBSET ModuleNodeId,
      (**********************************************************************)
      (* The top-level submodules that appear in this module.               *)
      (**********************************************************************)
    theorems : SUBSET ExprNodeId,
    assumes  : SUBSET ExprNodeId,
      (**********************************************************************)
      (* In this representation, a theorem or assumption node points to an  *)
      (* ExprNode.                                                          *)
      (**********************************************************************)
    levelConstraints    : SUBSET LevelConstraint,
    argLevelConstraints : SUBSET ArgLevelConstraint,
    argLevelParams      : SUBSET ArgLevelParam]
      (**********************************************************************)
      (* The meanings of these sets of constraints are described with the   *)
      (* definitions of the constraint data types.  The parameters that     *)
      (* appear in them are the declared constants and variables of the     *)
      (* module.  These constraints are used to check the legality of       *)
      (* instantiation if this is a constant module.  For a non-constant    *)
      (* module, these fields are not needed, because declared constant     *)
      (* operators can be instantiated only with constant operators.  For a *)
      (* constant module, the levelConstraints and argLevelConstraints      *)
      (* fields reflect only constraints that prevent constants from being  *)
      (* instantiated with temporal (level 3) formulas.                     *)
      (*                                                                    *)
      (* The MaxLevels method of the api is defined in terms of             *)
      (* levelConstraints as follows.  If id is the NodeId of the i-th      *)
      (* declared constant, and mod is the ModuleNodeId, then               *)
      (*                                                                    *)
      (*    MaxLevels(i) =                                                  *)
      (*      IF mod.constantModule                                         *)
      (*        THEN MinLevelConstraint(id, mod.levelConstraints)           *)
      (*        ELSE 0                                                      *)
      (**********************************************************************)

 OpDefOrDeclNodeFields ==
   (*************************************************************************)
   (* This defines the fields that are common to the OpDeclNode and         *)
   (* OpDefNode types.                                                      *)
   (*************************************************************************)
   [name : STRING,
      (**********************************************************************)
      (* The name of the operator.  (This isn't used in the level           *)
      (* computation, but it's convenient for keeping track of things when  *)
      (* running tests of the spec with TLC.)                               *)
      (**********************************************************************)

    numberOfArgs : Nat,
      (**********************************************************************)
      (* The number of arguments of the operator.  Operators that can take  *)
      (* an arbitrary number of arguments are represented by an infinite    *)
      (* sequence of definitions, one for each possible number of           *)
      (* arguments.  For example, we pretend that there is a sequence of    *)
      (* operators Tuple0, Tuple1, Tuple2, ...  such that <<a, b>> is       *)
      (* represented as Tuple2(a, b).                                       *)
      (**********************************************************************)
    level : LevelValue]
      (**********************************************************************)
      (* For an OpDeclNode op, the value of op.level is 0 except for one    *)
      (* representing a variable declaration, for which op.level equals 1.  *)
      (*                                                                    *)
      (* The meaning of op.level for an OpDefNode is described above.       *)
      (**********************************************************************)

 OpDeclNode ==
   (*************************************************************************)
   (* Represents a declared constant or variable.                           *)
   (*************************************************************************)
   RecordCombine([kind : {"ConstantDeclNode", "VariableDeclNode"}],
                 OpDefOrDeclNodeFields)

 OpDefNode ==
   (*************************************************************************)
   (* Represents a definition, for example the definition of the symbol Foo *)
   (* in Foo(A, B) == expr.  We also assume imaginary definitions of        *)
   (* built-in symbols.  Unlike in the actual SANY api, we represent a      *)
   (* construction like {exp : x \in S, y \in T} as something like          *)
   (* SetCons3(exp, S, T), where SetCons3 is an imaginary operator that     *)
   (* takes three arguments.  (As remarked above, we pretend that every     *)
   (* operator has a fixed number of arguments, so we pretend that there is *)
   (* also a separate OpDefNode for the operator SetCons4 used to represent *)
   (* the construction {exp : x \in S, y \in T, z \in U}.                   *)
   (*                                                                       *)
   (* As indicated by the formal semantics, a function definition           *)
   (*                                                                       *)
   (*   f[x \in S] == e                                                     *)
   (*                                                                       *)
   (* is treated like the definition                                        *)
   (*                                                                       *)
   (*   f == CHOOSE f : f = [x \in S |-> e]                                 *)
   (*                                                                       *)
   (* The level-constraint fields of the OpDefNode for an operator Op       *)
   (* reflects all the constraints implied by the body of the definition of *)
   (* Op for the parameters within whose scope the definition appears.      *)
   (* However, the argLevelParams field may contain arg-level parameters    *)
   (* whose op or param field (but not both) is a formal parameter of the   *)
   (* definition.  For example, consider                                    *)
   (*                                                                       *)
   (*    A(Op(_)) == LET B(c) == Op(c)                                      *)
   (*                IN  B(x')                                              *)
   (*                                                                       *)
   (* then the fact that the formal parameter c of B appears in the         *)
   (* definition of B in the argument of Op tells us that the expression    *)
   (* B(x') in the definition of A implies that A can be used only with a   *)
   (* first argument that can take an argument of level 2.  This is         *)
   (* recorded by the arg-level parameter                                   *)
   (*                                                                       *)
   (*    [op |-> Op, idx |-> 1, param |-> c]                                *)
   (*                                                                       *)
   (* in B.argLevelParams.                                                  *)
   (*************************************************************************)
   RecordCombine(
     [kind : {"OpDefNode"},
      params : Seq(ConstantDeclNodeId),
        (********************************************************************)
        (* The formal parameters of the definition.                         *)
        (********************************************************************)
      maxLevels : Seq(LevelValue),
      weights   : Seq({0,1}),
      minMaxLevel : Seq(Seq(LevelValue)),
      opLevelCond : Seq(Seq(Seq(BOOLEAN))),
        (********************************************************************)
        (* All these fields are described above, except for opLevelCond.    *)
        (* For an OpDefNode op, op.opLevelCond[i][j][k] is true iff the     *)
        (* i-th argument of op is an operator argument opArg, and the       *)
        (* definition of op contains an expression in which the j-th formal *)
        (* parameter of the definition of op appears within the k-th        *)
        (* argument of opArg.  As we'll see, this information is needed for *)
        (* keeping track of level constraints.                              *)
        (********************************************************************)
      body : ExprNodeId \cup {Null},
        (********************************************************************)
        (* The body of the definition.  For a built-in operator, it's Null. *)
        (********************************************************************)
      substitution : SubstitutionNodeId],
        (********************************************************************)
        (* Suppose that a module M contains the definition                  *)
        (*                                                                  *)
        (*    Op(p, q) == expr                                              *)
        (*                                                                  *)
        (* and let mOp be the corresponding OpDef node for operator Op.     *)
        (* Next suppose that another module N contains                      *)
        (*                                                                  *)
        (*    MI(x) == INSTANCE M WITH A <- x+1, B <- x*r                   *)
        (*                                                                  *)
        (* This adds to module N the operator MI!Op such that               *)
        (*                                                                  *)
        (*    MI!Op(x, p, q) ==  Iexpr                                      *)
        (*                                                                  *)
        (* where Iexpr is the expression obtained from expr by substituting *)
        (* x+1 for A and x*r for B. (In TLA+ we write                       *)
        (* MI(exp1)!Op(exp2,exp3), but this is just syntax; MI!Op is an     *)
        (* operator that takes 3 arguments.)  The INSTANCE statement adds   *)
        (* to the semantic tree for module N a UserOpDef node miOp for the  *)
        (* operator MI!Op such that                                         *)
        (*                                                                  *)
        (*    miOp.name         = "MI!Op",                                  *)
        (*    miOp.numberOfArgs = 3                                         *)
        (*    miOp.params[1]    = a ref to a ConstantDeclNode for x         *)
        (*    miOp.params[2]    = mOp.params[1]                             *)
        (*    miOp.params[3]    = mOp.params[2]                             *)
        (*    miOp.body         = mOp.body                                  *)
        (*    miOp.substitution = a SubstitutionNode representing           *)
        (*                             A <- x+1, B <- x*r                   *)
        (*                                                                  *)
        (* For convenience, if Op does not come from an instantiated        *)
        (* module, we let the substitution field point to a null            *)
        (* substitution--that is, one whose subFor and subWith fields are   *)
        (* the empty sequence.                                              *)
        (********************************************************************)
     RecordCombine(OpDefOrDeclNodeFields, LevelConstraintFields))

 InstanceNode ==
   (*************************************************************************)
   (* Represents a statement of the form                                    *)
   (*                                                                       *)
   (*   I(param[1], ... , param[p]) ==                                      *)
   (*     INSTANCE M WITH mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]  *)
   (*                                                                       *)
   (* or simply                                                             *)
   (*                                                                       *)
   (*   INSTANCE M WITH mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]    *)
   (*                                                                       *)
   (* The mparam[i] are assumed to be all the declared constants and        *)
   (* variables of M.  (That is, implicit substitutions of the form         *)
   (* param <- param are made explicit.)                                    *)
   (*************************************************************************)
   [kind : {"InstanceNode"},
    module : ModuleNodeId,
        (********************************************************************)
        (* The instantiated module.                                         *)
        (********************************************************************)
    params : Seq(ConstantDeclNodeId),
        (********************************************************************)
        (* The formal parameters of the definition.                         *)
        (********************************************************************)
    substitution : SubstitutionNodeId ,
        (********************************************************************)
        (* The substitution.  If M has no parameters, then this is the null *)
        (* substitution with subFor and subWith fields equal to the empty   *)
        (* sequence.                                                        *)
        (********************************************************************)
    numberOfArgs : Nat,
    levelConstraints    : SUBSET LevelConstraint,
    argLevelConstraints : SUBSET ArgLevelConstraint,
    argLevelParams      : SUBSET ArgLevelParam]
      (**********************************************************************)
      (* The level constraints obtained from the instantiation.  (There are *)
      (* no level parameters for the InstanceNode itself.)                  *)
      (**********************************************************************)

 OpDefOrDeclNode == OpDefNode \cup OpDeclNode

 OpApplNode ==
   (*************************************************************************)
   (* An OppApplNode represents an operator application.  Examples of       *)
   (* expressions that such a node can represent are:                       *)
   (*                                                                       *)
   (*   A \cup B           which we think of as \cup(A, B)                  *)
   (*                                                                       *)
   (*   (x + y) * (b + c)  which we think of as *(+(x,y), +(b,c))           *)
   (*                                                                       *)
   (*   \E x, y \in S, <<u, v>> \in T : (x+y) > (u+v) which we think of     *)
   (*   here as something like:                                             *)
   (*                                                                       *)
   (*        \E(S, T, >(+(x,y), +(u,v)))                                    *)
   (*                                                                       *)
   (*   plus the declarations of x, y, u, and v.  (The OpApplNode in the    *)
   (*   actual API maintains the actual structure of the expression,        *)
   (*   Here, we don't bother to distinguish \E x, y, z \in S : P           *)
   (*   from \E <<x, y, z>> \in S : P                                       *)
   (*************************************************************************)
   RecordCombine(
     [kind : {"OpApplNode"},
      operator : OpDefOrDeclNodeId,
        (********************************************************************)
        (* The (id of the) OpDefOrDecl node of the operator.                *)
        (********************************************************************)
      args : Seq(ExprNodeId) \ {<<>>},
        (********************************************************************)
        (* An OpApplNode has a nonempty sequence of arguments.              *)
        (********************************************************************)
      quantSymbols : SUBSET BoundSymbolNodeId,
        (********************************************************************)
        (* The bound symbols introduced by the operator application.        *)
        (********************************************************************)
      level : LevelValue],
     LevelConstraintFields)

 SubstitutionNode ==
   (*************************************************************************)
   (* The Substitution object s that represents the WITH clause             *)
   (*                                                                       *)
   (*    A <- x+1, B <- x*r                                                 *)
   (*                                                                       *)
   (* has Len(s.subFor) = Len(s.subWith) = 2 and                            *)
   (*                                                                       *)
   (*    s.subFor[1]  = the id of the ConstantDecl or VariableDecl          *)
   (*                        node for A                                     *)
   (*    s.subFor[2]  = the id of the ConstantDecl or VariableDecl          *)
   (*                        node for B                                     *)
   (*    s.subWith[1] = the id of the ExprNode for x+1                      *)
   (*    s.subWith[2] = the id of the ExprNode for x*r                      *)
   (*                                                                       *)
   (* Note that the nodes referenced in subFor are in the semantic          *)
   (* tree for the instantiated module, while those referenced in           *)
   (* subWith are in the semantic tree for the instantiating module.        *)
   (*************************************************************************)
   [kind    : {"SubstitutionNode"},
    subFor  : Seq(OpDeclNodeId),
    subWith : Seq(ExprNodeId)]

 IdentifierNode ==
    (************************************************************************)
    (* An IdentifierNode is an ExprNode with a ref field.  It represents an *)
    (* expression that consists of a single symbol.  For example, the       *)
    (* OppApplNode that represents the expression A * (b + c) will have as  *)
    (* its list of arguments the subexpressions A and b+c.  The             *)
    (* subexpression A will be an IdentifierNode whose ref field returns    *)
    (* the OpDefOrDeclNode that declares or defines A.                      *)
    (************************************************************************)
    RecordCombine(
     [kind : {"IdentifierNode"},
      ref  : OpDefOrDeclNodeId \cup BoundSymbolNodeId,
      level : LevelValue],
     LevelConstraintFields)

 BoundSymbolNode ==
   (*************************************************************************)
   (* Represents a bounded identifier, like the x in {x \in S : x > 0}.  It *)
   (* has level 0 except for the bounded symbols introduced by \EE and \AA, *)
   (* which have level 1.                                                   *)
   (*************************************************************************)
   [kind  : {"BoundSymbolNode"},
    name  : STRING,
    level : {0,1}]

 LetInNode ==
   (*************************************************************************)
   (* This node represents a LET expression, for example                    *)
   (*                                                                       *)
   (*    LET Foo(a) == a + x                                                *)
   (*        Bar == Foo(a) + a                                              *)
   (*    IN  body                                                           *)
   (*************************************************************************)
    RecordCombine(
     [kind : {"LetInNode"},
      opDefs    : SUBSET OpDefNodeId,
      instances : SUBSET InstanceNodeId,
        (********************************************************************)
        (* The LET definitions and INSTANCE statements.                     *)
        (********************************************************************)
      body : ExprNodeId,
      level: LevelValue],
     LevelConstraintFields)

 ValueNode == RecordCombine(
   (*************************************************************************)
   (* This node type represents the NumeralNode, DecimalNode, and           *)
   (* StringNode, of the actual api.                                        *)
   (*************************************************************************)
     [kind  : {"ValueNode"},
      level : {0}],
     LevelConstraintFields)

 ExprNode == OpApplNode \cup LetInNode \cup ValueNode \cup IdentifierNode

 SemNode ==
   (*************************************************************************)
   (* The type (set of all possible) semantic nodes.                        *)
   (*************************************************************************)
   ModuleNode \cup OpDefOrDeclNode \cup InstanceNode \cup
      ExprNode \cup SubstitutionNode \cup BoundSymbolNode

 -----------------------------------------------------------------------------
 (***************************************************************************)
 (*                            "Type Correctness"                           *)
 (***************************************************************************)
 TypeOK ==
   (*************************************************************************)
   (* This expresses the basic type of Node, and also some relations among  *)
   (* the various fields of semantic nodes that aren't implied by the       *)
   (* simple data type definitions.                                         *)
   (*************************************************************************)
   /\ Node \in [NodeId -> SemNode]
   /\ \A id \in NodeId :
        LET n == Node[id]
        IN  /\ (n \in OpDefNode) =>
                 /\ Len(n.maxLevels) = n.numberOfArgs
                 /\ Len(n.weights)   = n.numberOfArgs
                 /\ Len(n.params) = n.numberOfArgs
                 /\ Len(n.minMaxLevel) = n.numberOfArgs
                 /\ Len(n.opLevelCond) = n.numberOfArgs
                 /\ \A i \in 1..n.numberOfArgs :
                      /\ Len(n.minMaxLevel[i]) = Node[n.params[i]].numberOfArgs
                      /\ Len(n.opLevelCond[i]) = n.numberOfArgs
                      /\ \A j \in 1..n.numberOfArgs :
                           Len(n.opLevelCond[i][j]) =
                              Node[n.params[i]].numberOfArgs

            /\ (n \in OpDeclNode) =>
                 /\ (n.kind = "ConstantDeclNode") => (n.level = 0)
                 /\ (n.kind = "VariableDeclNode") => /\ n.level = 1
                                                     /\ n.numberOfArgs = 0

            /\ (n \in OpApplNode) =>
                 (Len(n.args) = Node[n.operator].numberOfArgs)

            /\ (n \in SubstitutionNode) => (Len(n.subFor) = Len(n.subWith))

            /\ (n \in InstanceNode) =>
                 /\ n.numberOfArgs = Len(n.params)
                 /\ (********************************************************)
                    (* There is a WITH substitution for every parameter of  *)
                    (* the instantiated module.                             *)
                    (********************************************************)
                    LET mparamid ==
                          (**************************************************)
                          (* Defines the mparamid[i] to be the parameter    *)
                          (* ids of the WITH clause.                        *)
                          (**************************************************)
                          [i \in 1..Len(Node[n.substitution].subFor) |->
                              Node[n.substitution].subFor[i]]
                        M == Node[n.module]
                           (*************************************************)
                           (* The ModuleNode of the instantiated module.    *)
                           (*************************************************)
                    IN  M.opDecls = {mparamid[i] : i \in 1..Len(mparamid)}

 -----------------------------------------------------------------------------
 (***************************************************************************)
 (*                         Level Correctness Conditions                    *)
 (*                                                                         *)
 (* Level checking is defined by the predicate LevelCorrect, which is a     *)
 (* correctness condition relating the level fields of a semantic node to   *)
 (* those of its children.  From this condition, it's straightforward to    *)
 (* design a recursive procedure for computing those fields.  The           *)
 (* conditions for each kind of node are defined separately, where the      *)
 (* predicate xxxNodeLevelCorrect(n) defines the correctness condition on a *)
 (* node n of kind xxxNode.  The following operators are used in the        *)
 (* definition of LevelCorrect.                                             *)
 (***************************************************************************)

 IsOpArg(op, k) == Node[op.params[k]].numberOfArgs > 0
   (*************************************************************************)
   (* If op is an OpDefNode and k \in 1..op.numberOfArgs, then this is true *)
   (* iff the k-th argument of op is an operator argument.                  *)
   (*************************************************************************)

 SubstituteInLevelConstraint(rcd, subst) ==
   (*************************************************************************)
   (* If rcd is a record containing level-constraint fields and subst is a  *)
   (* substitution, then this is the record consisting of the               *)
   (* level-constraint fields inferred from those of rcd by the             *)
   (* substitution.  For example, if rcd is an ExprNode representing an     *)
   (* expression expr, then SubstituteInLevelConstraint(rcd, subst) is the  *)
   (* record of level constraints for the expression obtained from expr by  *)
   (* the substitution subst.                                               *)
   (*************************************************************************)
   LET paramNums == 1..Len(subst.subFor)
         (*******************************************************************)
         (* The set of substitution parameter numbers.                      *)
         (*******************************************************************)

       ParamSubst(id) ==
         (*******************************************************************)
         (* The set of "substitute parameters" of the parameter whose       *)
         (* NodeId is id.  If id is one of the parameters being substituted *)
         (* for in subst, then this is the set of LevelParams of the        *)
         (* expression being substituted for it; otherwise, it equals {id}. *)
         (*******************************************************************)
         IF \E i \in paramNums : subst.subFor[i] = id
           THEN LET subExpNum == CHOOSE i \in paramNums : subst.subFor[i] = id
                IN  Node[subst.subWith[subExpNum]].levelParams
           ELSE {id}

       IsOpParam(i) == Node[subst.subFor[i]].numberOfArgs > 0
         (*******************************************************************)
         (* True iff substitution parameter i is an operator parameter.     *)
         (*******************************************************************)

       argNums == 1..Len(subst.subFor)
         (*******************************************************************)
         (* The set of parameter numbers.                                   *)
         (*******************************************************************)

       SubOp(opid) ==
         (*******************************************************************)
         (* If opid is the NodeId of an operator parameter, then this       *)
         (* equals the NodeId of the operator with which this operator is   *)
         (* substituted for by subst, which is opid itself if subst does    *)
         (* not substitute for opid.                                        *)
         (*******************************************************************)
         IF \E i \in paramNums : subst.subFor[i] = opid
           THEN LET subExpNum ==
                      CHOOSE i \in paramNums : subst.subFor[i] = opid
                IN  Node[subst.subWith[subExpNum]].ref
           ELSE opid

   IN  [levelParams |->
          UNION {ParamSubst(id) : id \in rcd.levelParams},

        levelConstraints |->
          (******************************************************************)
          (* There are two kinds of level constraints obtained after        *)
          (* substitution: ones that come from rcd.levelConstraints via     *)
          (* substitution, and ones that come from elements alp in          *)
          (* rcd.argLevelParams because alp.op is a substitution parameter  *)
          (* replaced by a defined operator defOp, and                      *)
          (* defOp.maxLevels[alp.idx] implies level constraints on some     *)
          (* parameter in the expression substituted for alp.param.         *)
          (******************************************************************)
          LET Sub(lc) ==
                (************************************************************)
                (* If lc is a level constraint on a parameter param, then   *)
                (* this is the set of level constraints that implies        *)
                (* because param might be substituted for.                  *)
                (************************************************************)
                {[lc EXCEPT !.param = par] :
                    par \in ParamSubst(lc.param)}

              ALP(i) ==
                (************************************************************)
                (* The set of arg-level parameters alp such that alp.op is  *)
                (* the substitution parameter i.                            *)
                (************************************************************)
                {alp \in rcd.argLevelParams : alp.op = subst.subFor[i]}

             SubInALP(alp) ==
               (*************************************************************)
               (* The set of arg-level parameters obtained from arg-level   *)
               (* parameter alp by replacing alp.param with each of its     *)
               (* substitute parameters.                                    *)
               (*************************************************************)
                {[alp EXCEPT !.param = par] :
                    par \in ParamSubst(alp.param)}

              SubALP(i) == UNION {SubInALP(alp) : alp \in ALP(i)}
                (************************************************************)
                (* The set of all SubInALP(alp) with alp in ALP(i).         *)
                (************************************************************)

              LC(i, alp) ==
                (************************************************************)
                (* The level constraint implied by an element alp of        *)
                (* SubALP(i), if parameter i is an operator parameter       *)
                (* instantiated by a defined operator.                      *)
                (************************************************************)
                [param |-> alp.param,
                 level |->
                   Node[Node[subst.subWith[i]].ref].maxLevels[alp.idx]]

              OpDefParams ==
                {i \in paramNums : /\ IsOpParam(i)
                                   /\ Node[subst.subWith[i]].ref \in
                                        OpDefNodeId}
          IN  (UNION {Sub(lc) : lc \in rcd.levelConstraints})
                \cup
              (UNION { {LC(i, alp) : alp \in SubALP(i)} : i \in OpDefParams }),

        argLevelConstraints |->
          (******************************************************************)
          (* There are two kinds of arg-level constraints produced by the   *)
          (* substitution: ones obtained by substitution from               *)
          (* rcd.argLevelConstraints, and ones obtained as follows from an  *)
          (* element alp of rcd.argLevelParams.  Since an operator          *)
          (* parameter can be instantiated only with an operator,           *)
          (* ParamSubst(alp.op) consists of a single operator op.  If op is *)
          (* a declared operator, and the subst substitutes expression exp  *)
          (* for alp.param, then op must be able to accept argument alp.idx *)
          (* of level at least that of exp.  (If there's no substitution    *)
          (* for alp.param, then it is a parameter that has level 0, so it  *)
          (* generates no non-trivial arg-level constraint.)                *)
          (******************************************************************)
          LET Sub(alc) ==
                (************************************************************)
                (* The set of arg-level constraints that come from the      *)
                (* element alc.  This set contains zero or one element.     *)
                (* Note that if subst.subFor[i] is an operator parameter,   *)
                (* then subst.subWith[i] is an IdentifierNodeId.            *)
                (************************************************************)
                IF \E i \in 1..Len(subst.subFor) : subst.subFor[i] = alc.param
                  THEN LET subExpNum ==
                              CHOOSE i \in argNums :
                                         subst.subFor[i] = alc.param
                       IN  IF Node[subst.subWith[subExpNum]].ref \in
                                OpDeclNodeId
                             THEN {[alc EXCEPT !.param =
                                         Node[subst.subWith[subExpNum]].ref]}
                             ELSE {}
                  ELSE {alc}

             SubParamALP(i) ==
               (*************************************************************)
               (* The set of elements alp of rcd.argLevelParams such that   *)
               (* alp.param is substitution parameter number i.             *)
               (*************************************************************)
               {alp \in rcd.argLevelParams : alp.param = subst.subFor[i]}

             ALC(alp, i) ==
               (*************************************************************)
               (* The set of arg-level constraints (containing 0 or one     *)
               (* constraint) implied by an arg-level constraint alp in     *)
               (* SubParamALP(i).  Note that such an alp implies a          *)
               (* constraint iff SubOp(alp.op) is a declared (and not       *)
               (* defined) operator.                                        *)
               (*************************************************************)
               IF SubOp(alp.op) \in OpDeclNodeId
                 THEN {[param |-> SubOp(alp.op),
                        idx   |-> alp.idx,
                        level |-> Node[subst.subWith[i]].level]}
                 ELSE {}

             ALCSet(i) == UNION {ALC(alp, i) : alp \in SubParamALP(i)}
               (*************************************************************)
               (* The set of all level constraints implied by elements of   *)
               (* SubParamALP(i).                                           *)
               (*************************************************************)

          IN  (UNION {Sub(alc) : alc \in rcd.argLevelConstraints})
                \cup
              (UNION {ALCSet(i) : i \in paramNums}),

        argLevelParams |->
          (******************************************************************)
          (* The set of arg-level parameters implied by rcd.argLevelParams  *)
          (* after performing the substitution.  If arg-level parameter alp *)
          (* indicates that the parameter with index pId occurs in the j-th *)
          (* argument of opParam, then the substitution implies that any    *)
          (* element of ParamSubst(pId) occurs in the j-th argument of the  *)
          (* operator with which opParam is replaced by the substitution    *)
          (* (which may be itself).  If opParam is replaced by a defined    *)
          (* operator (and not a declared one), then this produces a        *)
          (* legality condition on the substitution, rather than a new      *)
          (* arg-level parameter.                                           *)
          (******************************************************************)
          LET Sub(alp) ==
                (************************************************************)
                (* The set of elements in SubArgLevelParams(ALP, subst)     *)
                (* that come from the element alp.                          *)
                (************************************************************)
                IF SubOp(alp.op) \in OpDeclNodeId
                  THEN {[alp EXCEPT !.op = SubOp(alp.op), !.param = pId] :
                           pId \in ParamSubst(alp.param)}
                  ELSE {}
          IN  UNION {Sub(alp) : alp \in rcd.argLevelParams} ]

 ReducedLevelConstraint(rcd, paramSet) ==
   (*************************************************************************)
   (* If rcd is a record with level-constraint fields, then this is the     *)
   (* record obtained by removing from those level-constraint fields all    *)
   (* constraints on the parameters in paramSet.                            *)
   (*************************************************************************)
   [rcd EXCEPT
     !.levelParams = @ \ paramSet,
     !.levelConstraints  = {lc \in @ : lc.param \notin paramSet},
     !.argLevelConstraints = {alc \in @ : alc.param \notin paramSet},
     !.argLevelParams = {alp \in @ : /\ alp.op \notin paramSet
                                     /\ alp.param \notin paramSet}]


 -----------------------------------------------------------------------------
 (***************************************************************************)
 (* The predicate LevelCorrect is defined in terms of the following         *)
 (* operators, which each define level-correctness for one kind of node.    *)
 (* In each definition, the first conjunct is the condition for the node to *)
 (* be level-correct, unless there is a comment indicating that there is no *)
 (* level-correctness condition for that kind of node.  In all cases,       *)
 (* level-correctness of the child nodes is assumed when expressing         *)
 (* level-correctness of a node.                                            *)
 (***************************************************************************)
 ModuleNodeLevelCorrect(n) ==
   (*************************************************************************)
   (* We assume n is a ModuleNode.  It is level-correct iff all the         *)
   (* definitions, instances, theorems, and assumes are, and all the        *)
   (* assumes have level 0.                                                 *)
   (*                                                                       *)
   (* The level constraints come from the level constraints of the          *)
   (* definitions, instances, theorems, and assumes in the obvious way.     *)
   (*************************************************************************)
   LET defParams(opid) ==
         (*******************************************************************)
         (* The set of node ids of the formal parameter of the definition   *)
         (* represented by the node with id opid.                           *)
         (*******************************************************************)
         {Node[opid].params[i] : i \in 1..Node[opid].numberOfArgs}

       nonDefs == n.instances \cup n.theorems \cup n.assumes
         (*******************************************************************)
         (* All nodes contributing to the level constraints other than      *)
         (* OpDef nodes.                                                    *)
         (*******************************************************************)

       allDefs == n.opDefs \cup nonDefs

   IN  /\ (******************************************************************)
          (* Level correctness.                                             *)
          (******************************************************************)
          \A id \in n.assumes : Node[id].level = 0

       /\ n.levelConstraints =
            UNION {Node[opid].levelConstraints : opid \in allDefs}

       /\ n.argLevelConstraints =
            UNION {Node[opid].argLevelConstraints : opid \in allDefs}

       /\ n.argLevelParams =
            (****************************************************************)
            (* We must remove the constraints on formal parameters of the   *)
            (* definitions.                                                 *)
            (****************************************************************)
            (UNION {ReducedLevelConstraint(
                        Node[opid],
                        defParams(opid)).argLevelParams :
                     opid \in n.opDefs})
             \cup
            UNION {Node[opid].argLevelParams : opid \in nonDefs}


 InstanceNodeLevelCorrect(n) ==
   (*************************************************************************)
   (* We assume n is an InstanceNode representing                           *)
   (*                                                                       *)
   (*   I(param[1], ... , param[p]) ==                                      *)
   (*     INSTANCE M WITH mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]  *)
   (*************************************************************************)
   LET r == Len(Node[n.substitution].subWith)
       mexp == [i \in 1..r |-> Node[Node[n.substitution].subWith[i]]]
         (*******************************************************************)
         (* mexp[i] is an Expr node.                                        *)
         (*******************************************************************)
       paramIds == {n.params[i] : i \in 1..n.numberOfArgs}
         (*******************************************************************)
         (* The set of node ids {param[1], ... , param[p]}.                 *)
         (*******************************************************************)
       redMexp ==
         (*******************************************************************)
         (* Defines redMexp[i] to be the record that's the same as mexp[i]  *)
         (* except with all constraints on the param[i] removed.            *)
         (*******************************************************************)
         [i \in 1..r |-> ReducedLevelConstraint(mexp[i], paramIds)]
       M == Node[n.module]
         (*******************************************************************)
         (* M is the ModuleNode of the instantiated module.                 *)
         (*******************************************************************)
       mparamId == [i \in 1..r |-> Node[n.substitution].subFor[i]]
         (*******************************************************************)
         (* Defines mparamId[i] to be the NodeId for mparam[i].             *)
         (*******************************************************************)
       mparam == [i \in 1..r |-> Node[mparamId[i]]]
         (*******************************************************************)
         (* Defines mparam[i] to be the OpDeclNode for this parameter of M. *)
         (*******************************************************************)
       mOpArg(i) == Node[mexp[i].ref]
         (*******************************************************************)
         (* If mparam[i] is an operator argument, then mexp[i] is an        *)
         (* Identifier node for the OpDefOrDeclNode mOpArg(i).              *)
         (*******************************************************************)
       subst == Node[n.substitution]
         (*******************************************************************)
         (* The substitution node.                                          *)
         (*******************************************************************)
       MSubConstraints ==
         (*******************************************************************)
         (* A record consisting of the constraints obtained from M after    *)
         (* performing the substitutions.  The level parameters of M are    *)
         (* its declared constants.                                         *)
         (*******************************************************************)
         SubstituteInLevelConstraint(
           [levelParams         |-> {op \in M.opDecls : Node[op].level = 0},
            levelConstraints    |-> M.levelConstraints,
            argLevelConstraints |-> M.argLevelConstraints,
            argLevelParams      |-> M.argLevelParams],
           subst)
       redMSubConstraints ==
         (*******************************************************************)
         (* The constraint record MSubConstraints with the constraints on   *)
         (* the param[i] removed.                                           *)
         (*******************************************************************)
         ReducedLevelConstraint(MSubConstraints, paramIds)

   IN  (*********************************************************************)
       (* There are four level-correctness requirements on the              *)
       (* instantiation.  The first applies to nonconstant modules.  The    *)
       (* last three come from the level constraints of M. These three      *)
       (* requirements are trivially implied by the first requirement if M  *)
       (* is a nonconstant module, so they apply only when M is a constant  *)
       (* module.                                                           *)
       (*********************************************************************)
       /\ (******************************************************************)
          (* If M is a nonconstant module, then declared constants of M can *)
          (* be instantiated only with constant expressions, and the        *)
          (* declared variables only with expressions of level 1.           *)
          (******************************************************************)
          ~M.isConstant =>
             \A i \in 1..r : mexp[i].level \leq mparam[i].level

       /\ (******************************************************************)
          (* A level-constraint on mparam[i] implies a condition on         *)
          (* mexp[i].                                                       *)
          (******************************************************************)
          \A i \in 1..r :
             mexp[i].level \leq
                  MinLevelConstraint(mparamId[i], M.levelConstraints)

       /\ (******************************************************************)
          (* If mexp[i] is a defined operator argument, then an arg-level   *)
          (* constraint on mparam[i] implies a condition on mexp[i].        *)
          (******************************************************************)
          \A i \in 1..r :
             /\ mparam[i].numberOfArgs > 0
             /\ mOpArg(i) \in OpDefNode
             (***************************************************************)
             (* IF param[i] is an operator argument and mexp[i] is a        *)
             (* defined operator,                                           *)
             (***************************************************************)
             => (************************************************************)
                (* THEN the operator mexp[i] must satisfy the arg-level     *)
                (* constraints on param[i].                                 *)
                (************************************************************)
                \A j \in 1..mOpArg(i).numberOfArgs :
                   mOpArg(i).maxLevels[j] \geq
                      MaxArgLevelConstraints(mparamId[i],
                                             M.argLevelConstraints)[j]
       /\ (******************************************************************)
          (* An arg-level parameter of M asserting that param[j] appears in *)
          (* an argument of operator parameter param[i], where mexp[i] is a *)
          (* defined operator, implies a condition relating mexp[i] and     *)
          (* mexp[j].                                                       *)
          (******************************************************************)
          \A alp \in M.argLevelParams :
            \A i, j \in 1..r :
               /\ alp.op    = mparamId[i]
               /\ alp.param = mparamId[j]
               /\ mOpArg(i) \in OpDefNode
               => (mexp[j].level \leq mOpArg(i).maxLevels[alp.idx])

       (*********************************************************************)
       (* The level constraints for InstanceNode n are the ones that come   *)
       (* from performing the substitution in the level constraints of M    *)
       (* and from the mexp[i], except with constraints on the param[j]     *)
       (* removed.                                                          *)
       (*********************************************************************)
       /\ n.levelConstraints =
            redMSubConstraints.levelConstraints \cup
              UNION {redMexp[i].levelConstraints : i \in 1..r}
       /\ n.argLevelConstraints =
            redMSubConstraints.argLevelConstraints \cup
              UNION {redMexp[i].argLevelConstraints : i \in 1..r}
       /\ n.argLevelParams =
            redMSubConstraints.argLevelParams \cup
              UNION {redMexp[i].argLevelParams : i \in 1..r}

 OpDefNodeLevelCorrect(n) ==
   (*************************************************************************)
   (* We assume that n is an OpDefNode that is represents the definition of *)
   (*   Op(param[1], ... , param[p]) == exp                                 *)
   (*                                                                       *)
   (* Note that this definition may have been imported from a statement     *)
   (*                                                                       *)
   (*    Inst(param[1], ... , param[q]) ==                                  *)
   (*       INSTANCE M with                                                 *)
   (*          WITH mparam[1] <- mexp[1], ... , mparam[r] <- mexp[r]        *)
   (*                                                                       *)
   (* where Op is Inst!MOp.  In this case, we let exp be the body of the    *)
   (* definition of MOp, and subst be the substitution node of the INSTANCE *)
   (* statement.  We let subExp be the expression obtained by performing    *)
   (* the substitution.  We never explicitly compute subExp.  However, we   *)
   (* do compute some of the level constraints that subExp implies.         *)
   (*                                                                       *)
   (* Level-correctness of the substitutions, as well as constraints        *)
   (* imposed by the substitutions on the parameters within whose scope the *)
   (* INSTANCE statement appears, are handled by the correctness condition  *)
   (* on the INSTANCE statement.  However, the constraints implied by the   *)
   (* substitutions on the param[i] can yield constraints on the definition *)
   (* of Op.                                                                *)
   (*                                                                       *)
   (* We consider the ordinary (non-instantiated definition) case to be the *)
   (* special case of an instantiated definition with a null substitution.  *)
   (*                                                                       *)
   (* The definition is level-correct iff expression exp is.                *)
   (*************************************************************************)
   LET p == n.numberOfArgs
       param == n.params
       paramIds == {param[i] : i \in 1..p}
         (*******************************************************************)
         (* The set of ids of the formal parameters param[i].               *)
         (*******************************************************************)
       exp == Node[n.body]
         (*******************************************************************)
         (* The ExprNode representing the body of the definition.           *)
         (*******************************************************************)
       subst == Node[n.substitution]
       r == Len(Node[n.substitution].subWith)
       iParamIds == {param[i] : i \in 1..r}
         (*******************************************************************)
         (* The set of param[i] that come from the INSTANCE.                *)
         (*******************************************************************)
       mparamId == Node[n.substitution].subFor
         (*******************************************************************)
         (* mparamId[i] is the NodeId of mparam[i].                         *)
         (*******************************************************************)
       mexp == [i \in 1..r |-> Node[Node[n.substitution].subWith[i]]]
         (*******************************************************************)
         (* mexp[i] is the ExprNode of the i-th WITH expression.            *)
         (*******************************************************************)
       subExp == SubstituteInLevelConstraint(exp, subst)
         (*******************************************************************)
         (* This is a record containing the level-constraint fields for the *)
         (* expression subExp, obtained by performing the substitution      *)
         (* subst on exp.  (We do things in this way so that, if you want   *)
         (* to ignore the substitution and understand just how things work  *)
         (* for an ordinary definition, you can just replace subExp with    *)
         (* exp.  Of course, for the null substitution, these fields are    *)
         (* the same as the corresponding fields of exp.)                   *)
         (*******************************************************************)

   IN  /\ n.level =
            (****************************************************************)
            (* The level of Op is the maximum of                            *)
            (*   - The level of exp, and                                    *)
            (*   - The levels of all mexp[i] such that mparam[i]            *)
            (*     contributes  to the level of exp.                        *)
            (****************************************************************)
            LET pLevel(i) == IF mparamId[i] \in subExp.levelParams
                               THEN mexp[i].level
                               ELSE 0
            IN  NumMax(exp.level, SetMax({pLevel(i) : i \in 1..r}))

       /\ n.maxLevels =
            (****************************************************************)
            (* n.maxLevels[i] is determined by the level constraints on     *)
            (* param[i] that come from subExp and from the mexp[j].  (The   *)
            (* latter constraints can only be on param[i] with i \leq q.)   *)
            (* This is conservative, because it can imply a constraint on   *)
            (* an INSTANCE parameter (a param[i] with i \leq q) even if     *)
            (* that parameter doesn't appear in subExp.  However, we are    *)
            (* not keeping enough information to be more liberal, because   *)
            (* an appearance of that parameter in subExp would imply the    *)
            (* constraint, even if that appearance doesn't contribute to    *)
            (* the level of subExp (and hence the parameter doesn't occur   *)
            (* in subExp.levelParams).                                      *)
            (****************************************************************)
            [i \in 1..p |->
              MinLevelConstraint(
                param[i],
                subExp.levelConstraints \cup
                   UNION {mexp[j].levelConstraints : j \in 1..r})]

       /\ n.weights =
            (****************************************************************)
            (* n.weights[i] is 1 iff param[i] is a level parameter of       *)
            (* subExp.                                                      *)
            (****************************************************************)
            [i \in 1..p |-> IF param[i] \in subExp.levelParams THEN 1 ELSE 0]

       /\ n.minMaxLevel =
            (****************************************************************)
            (* n.minMaxLevel[i] is deduced from the arg-level constraints   *)
            (* on param[i] obtained from subExp and (for i \leq r) from the *)
            (* mexp[j].  As with n.maxLevels, this is conservative,         *)
            (* essentially assuming that any INSTANCE parameter could       *)
            (* appear in subExp.                                            *)
            (****************************************************************)
            [i \in 1..p |->
              MaxArgLevelConstraints(
                  param[i],
                  subExp.argLevelConstraints \cup
                    UNION {mexp[j].argLevelConstraints : j \in 1..r})]

       /\ n.opLevelCond =
            (****************************************************************)
            (* n.opLevelCond[i][j][k] is true iff there is an element of    *)
            (* subExp.argLevelParams indicating that param[j] occurs inside *)
            (* the k-th argument of an instance of param[i] in subExp or in *)
            (* some mexp[h].  Again, we are being conservative about        *)
            (* INSTANCE parameters.  Note that the arg-level parameters     *)
            (* that come from mexp[h] involve only the first r formal       *)
            (* parameters.                                                  *)
            (****************************************************************)
            [i \in 1..p |->
              [j \in 1..p |->
                [k \in 1..Node[param[i]].numberOfArgs |->
                  [op |-> param[i], idx |-> k, param |-> param[j]]
                   \in subExp.argLevelParams \cup
                        UNION {mexp[h].argLevelParams : h \in 1..r}]]]

       /\ n.levelParams = subExp.levelParams \ paramIds
            (****************************************************************)
            (* The level parameters of Op are the ones that come from       *)
            (* subExp that are not formal parameters.                       *)
            (****************************************************************)

       /\ n.levelConstraints =
            (****************************************************************)
            (* The level constraints of Op are the ones from subExp that    *)
            (* don't constrain its formal parameters.  The level            *)
            (* constraints that come from the mexp[j] belong to the         *)
            (* INSTANCE node.                                               *)
            (****************************************************************)
            {lc \in subExp.levelConstraints : lc.param \notin paramIds}

       /\ n.argLevelConstraints =
            (****************************************************************)
            (* The arg-level constraints of Op are the ones from subExp     *)
            (* that don't constraint its formal parameters.  Again, the     *)
            (* arg-level constraints that come from the mexp[j] belong to   *)
            (* the INSTANCE node.                                           *)
            (****************************************************************)
            {alc \in subExp.argLevelConstraints : alc.param \notin paramIds }

       /\ n.argLevelParams =
            (****************************************************************)
            (* The arg-level parameters of Op are the ones from subExp such *)
            (* that the op and params fields are not both formal parameters *)
            (* of Op, and the ones from the mexp[j] in which exactly one of *)
            (* those fields is a formal parameter of Op.  (The ones in      *)
            (* which both are formal parameters are represented in          *)
            (* n.opLevelCond; the ones in which neither are formal          *)
            (* parameters are in the argLevelParams field of the INSTANCE   *)
            (* node.)  Again we are being conservative with INSTANCE        *)
            (* parameters.  Such conservatism seems necessary--for example, *)
            (* in case the INSTANCE occurs within a LET.                    *)
            (****************************************************************)
            {alp \in subExp.argLevelParams : \/ alp.op    \notin paramIds
                                             \/ alp.param \notin paramIds }
              \cup
            {alp \in UNION {mexp[j].argLevelParams : j \in 1..r}:
               \/ /\ alp.op    \in    paramIds
                  /\ alp.param \notin paramIds
               \/ /\ alp.op    \notin paramIds
                  /\ alp.param \in    paramIds }


 (***************************************************************************)
 (* The definition of OpApplNodeLevelCorrect is rather complicated.  There  *)
 (* are two cases: an application of a declared operator and of a defined   *)
 (* operator.  These two cases are defined separately as                    *)
 (* DeclaredOpApplNodeLevelCorrect and DefinedOpApplNodeLevelCorrect.       *)
 (***************************************************************************)
 DeclaredOpApplNodeLevelCorrect(n) ==
   (*************************************************************************)
   (* This definition assumes that n is an OpApplNode representing the      *)
   (* expression Op(arg[1], ...  , arg[p]), where Op is a declared          *)
   (* operator represented by a Node op with NodeId opid.  We let the       *)
   (* formal parameters of the definition of Op be param[1], ...  ,         *)
   (* param[p].                                                             *)
   (*                                                                       *)
   (* The expression n is always level-correct (if its arguments are).      *)
   (*************************************************************************)
   LET (*********************************************************************)
       (* We first define arg, p, op, and param to have the meanings        *)
       (* described informally above.                                       *)
       (*********************************************************************)
       p     == Len(n.args)
       arg   == [i \in 1..p |-> Node[n.args[i]]]
         (*******************************************************************)
         (* arg[i] is the ExprNode representing the i-th argument of the    *)
         (* expression represented by n.                                    *)
         (*******************************************************************)
       opid == n.operator
       op   == Node[opid]
         (*******************************************************************)
         (* The OpDefNode of the operator Op.)                              *)
         (*     ^^^^^^^^^                                                   *)
         (* I believe this shold be OpDeclNode. (LL, Mar 2007)              *)
         (*******************************************************************)
       param == op.params
   IN  /\ n.level = NumMax(op.level,
                        SetMax({arg[i].level : i \in 1..p}))
            (****************************************************************)
            (* For an operator parameter, we assume that the weights of     *)
            (* each argument are 1, so the level is the maximum of the      *)
            (* levels of the arg[i], and of its own level.                  *)
            (*                                                              *)
            (* Corrected (I hope) on 24 Mar 2007 by LL to include op.level. *)
            (****************************************************************)
       /\ n.levelParams =
            (****************************************************************)
            (* The level parameters of n are the Op itself and the          *)
            (* LevelParams of all the arguments.                            *)
            (****************************************************************)
            {opid} \cup UNION {arg[i].levelParams : i \in 1..p}

       /\ n.levelConstraints =
            (****************************************************************)
            (* The LevelConstraints of n are all obtained from its          *)
            (* arguments.                                                   *)
            (****************************************************************)
            UNION {arg[i].levelConstraints : i \in 1..p}

       /\ n.argLevelConstraints =
            (****************************************************************)
            (* There are two source of arg-level constraints for n: the     *)
            (* ones it implies about Op, and the ones it inherits from its  *)
            (* arguments.                                                   *)
            (****************************************************************)
            {[op |-> opid, idx |-> i, level |-> arg[i].level] : i \in 1..p}
             \cup
            UNION {arg[i].argLevelConstraints : i \in 1..p}

       /\ n.argLevelParams =
            (****************************************************************)
            (* There are two source of arg-level parameters for n: the ones *)
            (* it implies about Op, and the ones it inherits from its       *)
            (* arguments.                                                   *)
            (****************************************************************)
            (LET ALP(i) ==
                   (*********************************************************)
                   (* The arg-level parameters implied about Op by the i-th *)
                   (* argument of n.                                        *)
                   (*********************************************************)
                   {[op |-> opid, idx   |-> i, param |-> par] :
                       par \in arg[i].levelParams}
             IN  UNION {ALP(i) : i \in 1..p} )
               \cup
            UNION {arg[i].argLevelParams : i \in 1..p}

 DefinedOpApplNodeLevelCorrect(n) ==
   (*************************************************************************)
   (* This definition assumes that n is an OpApplNode representing the      *)
   (* expression Op(arg[1], ...  , arg[p]), where Op is a defined operator. *)
   (* We let the formal parameters of the definition of Op be               *)
   (* param[1], ...  , param[p].                                            *)
   (*************************************************************************)
   LET (*********************************************************************)
       (* We first define arg, p, op, and param to have the meanings        *)
       (* described informally above.                                       *)
       (*********************************************************************)
       p     == Len(n.args)
       arg   == [i \in 1..p |-> Node[n.args[i]]]
         (*******************************************************************)
         (* arg[i] is the ExprNode representing the i-th argument of the    *)
         (* expression represented by n.                                    *)
         (*******************************************************************)
       op    == Node[n.operator]
         (*******************************************************************)
         (* The OpDefNode of the operator Op.                               *)
         (*******************************************************************)
       param == op.params
       numOpArgs(i) == Node[param[i]].numberOfArgs
         (*******************************************************************)
         (* If the i-th argument of op is an operator argument, then this   *)
         (* is the number of arguments that that operator argument takes.   *)
         (*******************************************************************)
       defOpArgs ==
         (*******************************************************************)
         (* The set of i such that param[i] is an operator argument and     *)
         (* arg[i] is a defined operator.                                   *)
         (*******************************************************************)
         {i \in 1..p : IsOpArg(op, i) /\ (arg[i].ref \in OpDefNodeId)}
       declOpArgs ==
         (*******************************************************************)
         (* The set of i such that param[i] is an operator argument and     *)
         (* arg[i] is an operator parameter.                                *)
         (*******************************************************************)
         {i \in 1..p : IsOpArg(op, i) /\ (arg[i].ref \in OpDeclNodeId)}
       OpLevelCondIdx(i,j) ==
         (*******************************************************************)
         (* The set of k such that op.opLevelCond[i][j][k] is defined and   *)
         (* equals TRUE.                                                    *)
         (*******************************************************************)
         {k \in 1..Node[param[i]].numberOfArgs : op.opLevelCond[i][j][k]}
   IN  /\ (******************************************************************)
          (* This conjunct expresses level-correctness.  For the i-th       *)
          (* argument, there is one condition derived from n.maxLevels[i]   *)
          (* and, if it is an operator argument and arg[i] is a defined     *)
          (* operator, then there is a condition derived from               *)
          (* n.minMaxLevel[i] and a condition derived from                  *)
          (* n.opLevelCond[i].                                              *)
          (******************************************************************)
          \A i \in 1..p :
            /\ arg[i].level \leq op.maxLevels[i]
                 (***********************************************************)
                 (* The level of arg[i] must be \leq op.maxLevels[i].       *)
                 (***********************************************************)

            /\ /\ IsOpArg(op, i)
                    (********************************************************)
                    (* IF arg[i] is an operator argument oparg ...          *)
                    (********************************************************)
               /\ arg[i].ref \in OpDefNodeId
                    (********************************************************)
                    (* ...  that is defined (rather than declared) [and     *)
                    (* hence is an IdentifierNode whose ref field is an     *)
                    (* OpDefOrDeclNodeId].)  THEN                           *)
                    (********************************************************)
               => /\ (*******************************************************)
                     (* oparg must be able to take a k-th argument of level *)
                     (* at least op.minMaxLevel[k].                         *)
                     (*******************************************************)
                     \A k \in 1.. numOpArgs(i) :
                       Node[arg[i].ref].maxLevels[k] \geq op.minMaxLevel[i][k]
                  /\ (*******************************************************)
                     (* If, in the definition of op, param[j] appears       *)
                     (* inside an expression in the k-th argument of        *)
                     (* param[i], then this means that, if we expand the    *)
                     (* definition of op in this expression, oparg will     *)
                     (* appear in a subexpression in which its k-th         *)
                     (* argument contains arg[j].  Hence, oparg must be     *)
                     (* able to take a k-th argument of level at least      *)
                     (* equal to the level of arg[j].                       *)
                     (*******************************************************)
                     \A j \in 1..p :
                       \A k \in 1..numOpArgs(i) :
                         op.opLevelCond[i][j][k] =>
                           arg[j].level \leq arg[i].maxLevels[k]

       /\ n.level =
            (****************************************************************)
            (* The maximum of op.level and the levels of all the arguments  *)
            (* whose corresponding weights are 1.                           *)
            (****************************************************************)
            NumMax(op.level,
                   SetMax({arg[i].level * op.weights[i] : i \in 1..p}))

       /\ n.levelParams =
            (****************************************************************)
            (* The parameters that contribute to the level of expression n  *)
            (* are the ones contributing to the level of op, together with  *)
            (* the ones contributing to the level of each argument that has *)
            (* weight 1.                                                    *)
            (****************************************************************)
            op.levelParams \cup
              LET LP(i) == IF op.weights[i] = 1 THEN arg[i].levelParams
                                                ELSE { }
              IN  UNION {LP(i) : i \in 1..p}

       /\ n.levelConstraints =
            (****************************************************************)
            (* Level constraints obtained from the expression arise from    *)
            (* the following sources:                                       *)
            (****************************************************************)
            (****************************************************************)
            (* 1. op.levelConstraints :                                     *)
            (*      Constraints inherited from the definition of op.        *)
            (****************************************************************)
            op.levelConstraints
               \cup
            (****************************************************************)
            (* 2. arg[i].levelConstraints :                                 *)
            (*      Constraints inherited from each argument arg[i].        *)
            (****************************************************************)
            (UNION {arg[i].levelConstraints : i \in 1..p})
               \cup
            (****************************************************************)
            (* 3. op.maxLevels[i] :                                         *)
            (*      If a parameter par contributes to the level of arg[i],  *)
            (*      then the level of par must be \leq op.maxLevels[i].     *)
            (****************************************************************)
            (LET LC(i) == {[param |-> par, level |-> op.maxLevels[i]] :
                              par \in arg[i].levelParams}
             IN  UNION {LC(i) : i \in 1..p})
              \cup
            (****************************************************************)
            (* 4. op.opLevelCond :                                          *)
            (*      If param[i] is an operator parameter, arg[i] is         *)
            (*      a defined operator opArg, and param[j] contributes to   *)
            (*      the level of the k-th argument of some occurrence of    *)
            (*      opArg in the definition of Op, then any parameter par   *)
            (*      contributing to the level of arg[j] must have level at  *)
            (*      most opArg.maxlevels[k].                                *)
            (****************************************************************)
            (LET LC(i,j,k) ==
               (*************************************************************)
               (* The set of level constraints that would be implied if a   *)
               (* parameter contributes to the level of arg[j], and         *)
               (* param[j] appears as the k-th argument of some instance of *)
               (* param[i] in the definition of the operator arg[i].        *)
               (*************************************************************)
                   {[param |-> par, level |-> Node[arg[i].ref].maxLevels[k]] :
                       par \in arg[j].levelParams}
                 LCE(i,j) ==
                   (*********************************************************)
                   (* The set of level constraints in all LC(i,j,k) such    *)
                   (* that param[i] is an operator parameter that takes at  *)
                   (* least k-th arguments, and op.opLevelCond[i][j][k]     *)
                   (* implies that param[j] appears as in k-th argument of  *)
                   (* some instance of param[i] in the definition of Op.    *)
                   (*********************************************************)
                   UNION {LC(i,j,k) : k \in OpLevelCondIdx(i,j)}
             IN  UNION {LCE(i,j) : i \in defOpArgs, j \in 1..p} )
              \cup
            (****************************************************************)
            (* 5. op.argLevelParams :                                       *)
            (*      For any arg-level parameter alp in op.argLevelParams,   *)
            (*      if alp.op = param[i] and arg[i] is a defined operator   *)
            (*      opArg, then the level of op.param must be \leq          *)
            (*      opArg.maxLevels[alp.idx].                               *)
            (****************************************************************)
            (LET
                 ALP(i) ==
                   (*********************************************************)
                   (* The set of arg-level parameters in op.argLevelParams  *)
                   (* whose op field is param[i].                           *)
                   (*********************************************************)
                   {alp \in op.argLevelParams : alp.op = param[i]}
                 LC(i) ==
                   (*********************************************************)
                   (* The level constraints implied by the elements in      *)
                   (* ALP(i).                                               *)
                   (*********************************************************)
                   {[param |-> alp.param,
                     level |-> Node[arg[i].ref].maxLevels[alp.idx]] :
                       alp \in ALP(i)}
             IN  UNION {LC(i) : i \in defOpArgs} )

        /\ n.argLevelConstraints =
            (****************************************************************)
            (* Arg-level constraints implied by the expression arise from   *)
            (* the following sources:                                       *)
            (****************************************************************)
            (****************************************************************)
            (* 1. op.argLevelConstraints                                    *)
            (*      Expression n inherits arg-level constraints from the    *)
            (*      definition of op.                                       *)
            (****************************************************************)
             op.argLevelConstraints
               \cup

            (****************************************************************)
            (* 2. arg[i].argLevelConstraints                                *)
            (*      Expression n inherits arg-level constraints from its    *)
            (*      arguments.                                              *)
            (****************************************************************)
             (UNION {arg[i].argLevelConstraints : i \in 1..p})
              \cup
            (****************************************************************)
            (* 3. op.minMaxLevel                                            *)
            (*     If arg[i] is a declared operator, then it must be able   *)
            (*     to take a k-th argument of level op.minMaxLevel[i][k].   *)
            (****************************************************************)
            (LET
                 ALC(i) ==
                   (*********************************************************)
                   (* If arg[i] is the IdentifierNode of a declared         *)
                   (* operator opArg, then these are the arg-level          *)
                   (* constraints implied by op.minMaxLevel for opArg.      *)
                   (*********************************************************)
                  {[param |-> arg[i].ref,
                    idx   |-> k,
                    level |-> op.minMaxLevel[i][k]] :
                      k \in 1..numOpArgs(i)}
             IN  UNION {ALC(i) : i \in declOpArgs})
               \cup
            (****************************************************************)
            (* 4. op.opLevelCond                                            *)
            (*      If op.opLevelCond[i][j][k] is true and arg[i] is an     *)
            (*      Identifier node referring to the declared operator      *)
            (*      opArg, then opArg must be able to take a k-th argument  *)
            (*      of level arg[j].level.                                  *)
            (****************************************************************)
            (LET ALC(i, j) ==
                   (*********************************************************)
                   (* If arg[i] is a declared operator, then this is the    *)
                   (* set of arg-level constraints implied for that         *)
                   (* operator by arg[j].level.                             *)
                   (*********************************************************)
                   {[param |-> arg[i].ref,
                     idx |-> k,
                     level |-> arg[j].level] : k \in OpLevelCondIdx(i,j)}

             IN  UNION {ALC(i,j) : i \in declOpArgs, j \in 1..p} )
               \cup
            (****************************************************************)
            (* 5. op.argLevelParams                                         *)
            (*      If an arg-level parameter alp indicates that param[i]   *)
            (*      appears as the k-th argument of a declared operator     *)
            (*      opArg, then n has an arg-level constraint indicating    *)
            (*      that opArg must be able to take a k-th argument of      *)
            (*      level arg[i].level.                                     *)
            (****************************************************************)
            (LET ALP(i) == {alp \in op.argLevelParams : alp.param = param[i]}
                   (*********************************************************)
                   (* The subset of op.argLevelParams whose param field is  *)
                   (* the i-th formal parameter of op.                      *)
                   (*********************************************************)
                 ALC(i) ==
                   (*********************************************************)
                   (* The set of arg-level constraints implied by the       *)
                   (* elements of ALP(i).                                   *)
                   (*********************************************************)
                   {[param |-> alp.param,
                     idx   |-> alp.idx,
                     level |-> arg[i].level] : alp \in ALP(i)}
              IN  UNION {ALC(i) : i \in 1..p})

       /\ n.argLevelParams =
            (****************************************************************)
            (* Arg-level parameters implied by the expression arise from    *)
            (* the following sources:                                       *)
            (****************************************************************)
            (****************************************************************)
            (* 1. arg[i].argLevelParams                                     *)
            (*      The expression inherits all arg-level parameters from   *)
            (*      its arguments.                                          *)
            (****************************************************************)
            (UNION {arg[i].argLevelParams : i \in 1..p})
             \cup
            (****************************************************************)
            (* 2. Elements alp of op.argLevelParams with neither alp.op or  *)
            (*    alp.param a formal parameter of the definition of op.     *)
            (****************************************************************)
            {alp \in op.argLevelParams :
              \A i \in 1..p : (alp.op # param[i]) /\ (alp.param # param[i])}
             \cup

            (****************************************************************)
            (* 3. Elements alp of op.argLevelParams with alp.op = param[i]. *)
            (*      If arg[i] is a declared operator opArg, then this       *)
            (*      implies an arg-level parameter asserting that alp.param *)
            (*      appears in argument alp.idx of opArg.                   *)
            (****************************************************************)
            (LET ALP(i) == {alp \in op.argLevelParams : alp.op = param[i]}
                   (*********************************************************)
                   (* The set of arg-level parameters alp of op with alp.op *)
                   (* = param[i].  (Note: we know that alp.param is not a   *)
                   (* formal parameter of op, because op.argLevelParams     *)
                   (* does not contain arg-level parameterss in which both  *)
                   (* the op and param fields are formal parameters of the  *)
                   (* definition of op.)                                    *)
                   (*********************************************************)
                 NLP(i) ==
                   (*********************************************************)
                   (* The arg-level parameters of the expression implied by *)
                   (* the elements of ALP(i).                               *)
                   (*********************************************************)
                   {[alp EXCEPT !.op = arg[i].ref] : alp \in ALP(i)}
             IN  UNION {NLP(i) : i \in declOpArgs})
               \cup
            (****************************************************************)
            (* 4. Elements alp of op.argLevelParams with alp.param =        *)
            (*    param[i].                                                 *)
            (*      This implies an arg-level parameter asserting that      *)
            (*      every parameter contributing to the level of arg[i]     *)
            (*      appears in argument alp.idx of an occurrence of         *)
            (*      alp.op.                                                 *)
            (****************************************************************)
            (LET OLP(i) ==
                   (*********************************************************)
                   (* The set of all arg-level parameters whose param field *)
                   (* is param[i].                                          *)
                   (*********************************************************)
                   {alp \in op.argLevelParams : alp.param = param[i]}
                 ALP(i) ==
                   (*********************************************************)
                   (* The set of arg-level parameters obtained from an      *)
                   (* arg-level parameter alp in op.argLevelParams by       *)
                   (* replacing alp.param with an element of                *)
                   (* arg[i].levelParams.                                   *)
                   (*********************************************************)
                   {[alp EXCEPT !.param = par] :
                      alp \in OLP(i), par \in arg[i].levelParams}
             IN  UNION {ALP(i) : i \in declOpArgs} )
              \cup
            (****************************************************************)
            (* 5. op.opLevelCond                                            *)
            (*      If op.opLevelCond[i][j][k] = TRUE and arg[i] is a       *)
            (*      declared operator opArg, then there are arg-level       *)
            (*      parameters declaring that every parameter contributing  *)
            (*      to the level of arg[j] appears in argument k of an      *)
            (*      occurrence of opArg.                                    *)
            (****************************************************************)
            (LET ALP(i,j) ==
                   (*********************************************************)
                   (* If arg[i] is a declared operator, then this is the    *)
                   (* set of all all arg-level parameters implied by        *)
                   (* op.opLevelCond[i][j] and arg[j].levelParams.          *)
                   (*********************************************************)
                   {[op |-> arg[i].ref, idx |-> k, param |-> par] :
                       k \in OpLevelCondIdx(i,j), par \in arg[j].levelParams}
              IN  UNION {ALP(i,j) : i \in declOpArgs, j \in 1..p})


 OpApplNodeLevelCorrect(n) ==
   IF n.operator \in OpDeclNodeId THEN DeclaredOpApplNodeLevelCorrect(n)
                                  ELSE DefinedOpApplNodeLevelCorrect(n)

 LetInNodeLevelCorrect(n) ==
   (*************************************************************************)
   (* We assume n is a LetInNode.                                           *)
   (*                                                                       *)
   (* A LetInNode is level-correct iff its children are.                    *)
   (*                                                                       *)
   (* The level constraints come from the IN expression together with the   *)
   (* LET definitions, except that the constraints on the definition's      *)
   (* formal parameters must be removed from the argLevelParams field of a  *)
   (* LET definition.                                                       *)
   (*************************************************************************)
   LET exp    == Node[n.body]
       letIds == n.opDefs \cup n.instances
       opParams(opid) ==
         (*******************************************************************)
         (* If opid is an OpDefNodeId, then this is the set of formal       *)
         (* parameters of the definition represented by Node[opid].         *)
         (*******************************************************************)
         {Node[opid].params[i] : i \in 1..Node[opid].numberOfArgs}
   IN  /\ n.level = exp.level
       /\ n.levelParams =
            exp.levelParams
       /\ n.levelConstraints =
            exp.levelConstraints \cup
               UNION {Node[opid].levelConstraints : opid \in letIds}
       /\ n.argLevelConstraints =
            exp.argLevelConstraints \cup
               UNION {Node[opid].argLevelConstraints : opid \in letIds}
       /\ n.argLevelParams =
            exp.argLevelParams
              \cup
            (UNION {ReducedLevelConstraint(Node[opid],
                                          opParams(opid)).argLevelParams :
                     opid \in n.opDefs})
              \cup
            UNION {Node[opid].argLevelParams : opid \in n.instances}


 IdentifierNodeLevelCorrect(n) ==
   (*************************************************************************)
   (* An IdentifierNode represents an expression that consists of a single  *)
   (* symbol, or else an operator argument appearing as the argument in the *)
   (* application of a higher-order operator.                               *)
   (*                                                                       *)
   (* It is always level-correct if its ref field is, which will be the     *)
   (* case except possibly for a defined operator argument                  *)
   (*************************************************************************)
   /\ n.level = Node[n.ref].level
        (********************************************************************)
        (* The level is the level of the symbol's node.                     *)
        (********************************************************************)
   /\ IF n.ref \in OpDeclNodeId \cup BoundSymbolNodeId
        THEN (***************************************************************)
             (* The symbol is a declared operator or a bound symbol.  In    *)
             (* this case, all the constraints are empty except for a       *)
             (* ConstantDeclNode, in which case the set of level parameters *)
             (* consists of the symbol itself.                              *)
             (***************************************************************)
             /\ n.levelParams         = IF n.ref \in ConstantDeclNodeId
                                          THEN {n.ref}
                                          ELSE { }
             /\ n.levelConstraints    = { }
             /\ n.argLevelConstraints = { }
             /\ n.argLevelParams      = { }

        ELSE (***************************************************************)
             (* The symbol is a defined operator (appearing as an argument  *)
             (* to a higher-order operator).  Its constraints are the       *)
             (* constraints of the symbol's OpDefNode.                      *)
             (***************************************************************)
             /\ n.levelParams         = Node[n.ref].levelParams
             /\ n.levelConstraints    = Node[n.ref].levelConstraints
             /\ n.argLevelConstraints = Node[n.ref].argLevelConstraints
             /\ n.argLevelParams      = Node[n.ref].argLevelParams

 LevelCorrect ==
   (*************************************************************************)
   (* The following kinds of nodes are always level-correct, and any level  *)
   (* information they contain is specified by their types.                 *)
   (*   OpDeclNode                                                          *)
   (*   ValueNode                                                           *)
   (*   OpDefNode for a built-in operator (one whose OpDefNode has a Null   *)
   (*      body)                                                            *)
   (*   BoundSymbolNode                                                     *)
   (*                                                                       *)
   (* The following nodes are level-correct iff their children are, and     *)
   (* they have no level constraints:                                       *)
   (*                                                                       *)
   (*   SubstitutionNode                                                    *)
   (*************************************************************************)
   \A id \in NodeId :
     LET n == Node[id]
     IN  /\ (n \in IdentifierNode) => IdentifierNodeLevelCorrect(n)
         /\ (n \in OpApplNode)     => OpApplNodeLevelCorrect(n)
         /\ n \in LetInNode        => LetInNodeLevelCorrect(n)
         /\ n \in InstanceNode     => InstanceNodeLevelCorrect(n)
         /\ n \in ModuleNode       => ModuleNodeLevelCorrect(n)
         /\ (n \in OpDefNode) /\ (n.body # Null) => OpDefNodeLevelCorrect(n)



 =============================================================================
