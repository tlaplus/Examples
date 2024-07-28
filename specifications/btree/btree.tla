\* Note: deletes have not been implemented
---- MODULE btree ----
EXTENDS TLC,
        Naturals,
        FiniteSets,
        Sequences

CONSTANTS Vals,
          MaxKey,
          MaxNode,
          MaxOccupancy,

          \* states
          READY,
          GET_VALUE,
          FIND_LEAF_TO_ADD,
          WHICH_TO_SPLIT,
          ADD_TO_LEAF,
          SPLIT_LEAF,
          SPLIT_INNER,
          SPLIT_ROOT_LEAF,
          SPLIT_ROOT_INNER,
          UPDATE_LEAF

Keys == 1..MaxKey
Nodes == 1..MaxNode

NIL == CHOOSE x : x \notin Nodes
MISSING == CHOOSE v : v \notin Vals


VARIABLES root,
          isLeaf, keysOf, childOf, lastOf, valOf,
          focus,
          toSplit,
          op, args, ret,
          state

TypeOk == /\ root \in Nodes
          /\ isLeaf \in [Nodes -> BOOLEAN]
          /\ keysOf \in [Nodes -> SUBSET Keys]
          /\ childOf \in [Nodes \X Keys -> Nodes \union {NIL}]
          /\ lastOf \in [Nodes -> Nodes \union {NIL}]
          /\ valOf \in [Nodes \X Keys -> Vals \union {NIL}]
          /\ focus \in Nodes \union {NIL}
          /\ toSplit \in Seq(Nodes)
          /\ op \in {"get", "insert", "update", NIL}
          /\ ret \in Vals \union {"ok", "error", MISSING, NIL}
          /\ state \in {READY, GET_VALUE, FIND_LEAF_TO_ADD, WHICH_TO_SPLIT, ADD_TO_LEAF, SPLIT_LEAF, SPLIT_INNER, SPLIT_ROOT_LEAF, SPLIT_ROOT_INNER, UPDATE_LEAF}

\* Max element in a set
Max(xs) == CHOOSE x \in xs : (\A y \in xs \ {x} : x > y)

\* Find the appropriate child node associated with the key
ChildNodeFor(node, key) ==
    LET keys == keysOf[node]
        maxKey == Max(keys)
        closestKey ==  CHOOSE k \in keys : /\ k>key
                                           /\ ~(\E j \in keys \ {k} : j>key /\ j<k)
    IN IF keys = {} \/ key >= maxKey
       THEN lastOf[node]
       \* smallest k that's bigger than key
       ELSE
       childOf[node, closestKey]


\* Identify the leaf node based on key
\* Find the leaf node associated with a key
RECURSIVE FindLeafNode(_, _)
FindLeafNode(node, key) ==
    IF isLeaf[node] THEN node ELSE FindLeafNode(ChildNodeFor(node, key), key)

AtMaxOccupancy(node) == Cardinality(keysOf[node]) = MaxOccupancy


\* We model a "free" (not yet part of the tree) node as one as a leaf with no keys
IsFree(node) == isLeaf[node] /\ keysOf[node] = {}

ChooseFreeNode == CHOOSE n \in Nodes : IsFree(n)


Init == /\ isLeaf = [n \in Nodes |-> TRUE]
        /\ keysOf = [n \in Nodes |-> {}]
        /\ childOf = [n \in Nodes, k \in Keys |-> NIL]
        /\ lastOf = [n \in Nodes |-> NIL]
        /\ valOf = [n \in Nodes, k \in Keys |-> NIL]
        /\ root = ChooseFreeNode
        /\ focus = NIL
        /\ toSplit = <<>>
        /\ op = NIL
        /\ args = NIL
        /\ ret = NIL
        /\ state = READY

GetReq(key) == 
    /\ state = READY
    /\ op' = "get"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ state' = GET_VALUE
    /\ UNCHANGED <<root, isLeaf, keysOf, childOf, lastOf, valOf, focus, toSplit>>

GetValue ==
    LET key == args[1] 
        node == FindLeafNode(root, key) IN
    /\ state = GET_VALUE
    /\ state' = READY
    /\ ret' = IF key \in keysOf[node] THEN valOf[node, key] ELSE MISSING
    /\ UNCHANGED <<root, isLeaf, keysOf, childOf, lastOf, valOf, focus, toSplit, args, op>>
    

InsertReq(key, val) ==
    /\ state = READY
    /\ op' = "insert"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ state' = FIND_LEAF_TO_ADD
    /\ UNCHANGED <<root, isLeaf, keysOf, childOf, lastOf, valOf, focus, toSplit>>

UpdateReq(key, val) ==
    LET leaf == FindLeafNode(root, key)
    IN /\ state = READY
       /\ op' = "update"
       /\ args' = <<key, val>>
       /\ ret' = NIL
       /\ focus' = leaf
       /\ state' = UPDATE_LEAF
       /\ UNCHANGED <<root, isLeaf, keysOf, childOf, lastOf, valOf, toSplit>>

UpdateLeaf ==
    LET key == args[1]
        val == args[2]
    IN /\ state = UPDATE_LEAF
       /\ valOf' = IF key \in keysOf[focus] THEN [valOf EXCEPT ![focus, key]=val] ELSE valOf
       /\ ret' = IF key \in keysOf[focus] THEN "ok" ELSE "error"
       /\ state' = READY
       /\ focus' = NIL
       /\ UNCHANGED <<root, isLeaf, keysOf, childOf, lastOf, toSplit, args, op>>

FindLeafToAdd ==
    LET key == args[1]
        leaf == FindLeafNode(root, key)
    IN /\ state = FIND_LEAF_TO_ADD
       /\ focus' = leaf
       /\ toSplit' = IF AtMaxOccupancy(leaf) THEN <<leaf>> ELSE <<>>
       /\ state' = IF AtMaxOccupancy(leaf) THEN WHICH_TO_SPLIT ELSE ADD_TO_LEAF
       /\ UNCHANGED <<root, isLeaf, keysOf, childOf, lastOf, valOf, args, op, ret>>


ParentOf(n) == CHOOSE p \in Nodes: \/ \E k \in Keys: n = childOf[p, k]
                                   \/ lastOf[p]=n

WhichToSplit ==
    LET  node == Head(toSplit)
         parent == ParentOf(node)
         splitParent == AtMaxOccupancy(parent)
         noMoreSplits == ~splitParent  \* if the parent doesn't need splitting, we don't need to consider more nodes for splitting
    IN /\ state = WHICH_TO_SPLIT
       /\ toSplit' =
           CASE node = root   -> toSplit
             [] splitParent   -> <<parent>> \o toSplit
             [] OTHER         -> toSplit
       /\ state' =
            CASE node # root /\ noMoreSplits /\ isLeaf[node]  -> SPLIT_LEAF
              [] node # root /\ noMoreSplits /\ ~isLeaf[node] -> SPLIT_INNER
              [] node = root /\ isLeaf[node]                  -> SPLIT_ROOT_LEAF
              [] node = root /\ ~isLeaf[node]                 -> SPLIT_ROOT_INNER
              [] OTHER                                        -> WHICH_TO_SPLIT
       /\ UNCHANGED <<root, isLeaf, keysOf, childOf, lastOf, valOf, op, args, ret, focus>>

\* Adding the <<key, val>> pair in args to the node indicated by focus
\* If the key is already present, this is an error
AddToLeaf ==
    LET key == args[1]
        val == args[2] IN
       /\ state = ADD_TO_LEAF
       /\ ret' = IF key \notin keysOf[focus] THEN "ok" ELSE "error"
       /\ keysOf' = IF key \notin keysOf[focus] THEN [keysOf EXCEPT ![focus]=@ \union {key}] ELSE keysOf
       /\ valOf' = IF key \notin keysOf[focus] THEN [valOf EXCEPT ![focus,key]=val] ELSE valOf
       /\ state' = READY
       /\ UNCHANGED <<root, isLeaf, childOf, lastOf, op, args, focus, toSplit>>

\* Return the pivot (midpoint) of a set of keys. If there are an even number of keys, bias towards the smaller one
PivotOf(keys) == CHOOSE k \in keys :
    LET smaller == {x \in keys : x < k}
        larger == {x \in keys: x > k} IN
     \/ Cardinality(smaller) = Cardinality(larger)
     \/ Cardinality(smaller) = Cardinality(larger)+1

SplitRootLeaf ==
    LET n1 == Head(toSplit)
        n2 == ChooseFreeNode
        newRoot == CHOOSE n \in Nodes : IsFree(n) /\ (n # n2)
        keys == keysOf[n1]
        pivot == PivotOf(keys)
        n1Keys == {x \in keys: x<pivot}
        n2Keys == {x \in keys: x>=pivot} 
        keyToInsert == args[1] IN
    /\ state = SPLIT_ROOT_LEAF
    /\ root' = newRoot
    /\ isLeaf' = [isLeaf EXCEPT ![newRoot]=FALSE, ![n2]=TRUE]
    /\ keysOf' = [keysOf EXCEPT ![newRoot]={pivot}, ![n1]=n1Keys, ![n2]=n2Keys]
    /\ childOf' = [childOf EXCEPT ![newRoot, pivot]=n1]
    /\ lastOf' = [lastOf EXCEPT ![newRoot]=n2]
    /\ valOf' = [n \in Nodes, k \in Keys |->
        CASE n=n1 /\ k \in n2Keys -> NIL
          [] n=n2 /\ k \in n2Keys -> valOf[n1, k]
          [] OTHER                -> valOf[n, k]]
    \* No more splits necessary, add the focus to the leaf
    \* Note that the focus may have changed due to the split
    /\ state' = ADD_TO_LEAF
    /\ focus' = IF keyToInsert < pivot THEN n1 ELSE n2
    /\ UNCHANGED <<op, args, ret, toSplit>>

ParentKeyOf(node) ==
    LET p == ParentOf(node) IN
    CHOOSE k \in keysOf[p]: childOf[p, k] = node

IsLastOfParent(node) == lastOf[ParentOf(node)] = node

SplitRootInner ==
    LET n1 == Head(toSplit)
        n2 == ChooseFreeNode
        newRoot == CHOOSE n \in Nodes : IsFree(n) /\ (n # n2)
        keys == keysOf[n1]
        pivot == PivotOf(keys)
        (* when splitting an inner node, pivot does not appear in either node, only in parent *)
        n1Keys == {x \in keys: x<pivot}
        n2Keys == {x \in keys: x>pivot} IN
    /\ state = SPLIT_ROOT_INNER
    /\ root' = newRoot
    /\ isLeaf' = [isLeaf EXCEPT ![newRoot]=FALSE, ![n2]=FALSE]
    /\ keysOf' = [keysOf EXCEPT ![newRoot]={pivot}, ![n1]=n1Keys, ![n2]=n2Keys]
    /\ childOf' = [n \in Nodes, k \in Keys |->
        CASE n=newRoot /\ k=pivot -> n1
          [] n=n1 /\ k \in n2Keys -> NIL
          [] n=n1 /\ k \in n1Keys -> childOf[n1, k]
          [] n=n2 /\ k \in n2Keys -> childOf[n1, k]
          [] OTHER                -> childOf[n, k]]
    /\ lastOf' = [lastOf EXCEPT ![newRoot]=n2, ![n1]=childOf[n1, pivot], ![n2]=lastOf[n1]]
    /\ toSplit' = <<>>
    /\ state' = ADD_TO_LEAF
    /\ UNCHANGED <<op, args, ret, focus, valOf>>

SplitLeaf ==
    LET n1 == Head(toSplit)
        n2 == ChooseFreeNode
        keys == keysOf[n1]
        pivot == PivotOf(keys)
        parent == ParentOf(n1)
        n1Keys == {x \in keys: x<pivot}
        n2Keys == {x \in keys: x>=pivot}
        keyToInsert == args[1]
    IN
    /\ state = SPLIT_LEAF
    /\ isLeaf' = [isLeaf EXCEPT ![n2]=TRUE]
    /\ keysOf' = [keysOf EXCEPT ![parent]=@ \union {pivot}, ![n1]=n1Keys, ![n2]=n2Keys]
    \* In the parent, point the pivot key to n1, and point the parent key to n2.
    \* TODO: handle the edge case where n1 was the last element
    /\ childOf' = IF IsLastOfParent(n1)
                  THEN [childOf EXCEPT ![parent, pivot]=n1]
                  ELSE [childOf EXCEPT ![parent, pivot]=n1, ![parent, ParentKeyOf(n1)]=n2]
    /\ lastOf' = IF IsLastOfParent(n1) THEN [lastOf EXCEPT ![parent]=n2] ELSE lastOf
    /\ valOf' = [n \in Nodes, k \in Keys |->
        CASE n=n1 /\ k \in n2Keys -> NIL
          [] n=n2 /\ k \in n2Keys -> valOf[n1, k]
          [] OTHER                -> valOf[n, k]]
    /\ state' = ADD_TO_LEAF
    /\ focus' = IF keyToInsert < pivot THEN n1 ELSE n2
    /\ UNCHANGED <<root, toSplit, op, args, ret>>


Next == \/ \E key \in Keys, val \in Vals : 
            \/ InsertReq(key, val)
            \/ UpdateReq(key, val)
        \/ \E key \in Keys: GetReq(key)
        \/ GetValue
        \/ FindLeafToAdd
        \/ WhichToSplit
        \/ AddToLeaf
        \/ SplitLeaf
        \/ SplitRootLeaf
        \/ SplitRootInner
        \/ UpdateLeaf

vars == <<root, isLeaf, keysOf, childOf, lastOf, valOf, focus, toSplit, op, args, ret, state>>

Spec == Init /\ [][Next]_vars /\ WF_op(\E key \in Keys: GetReq(key))

\*
\* Refinement mapping
\*

Leaves == {n \in Nodes : isLeaf[n]}

Mapping == INSTANCE kvstore
    WITH dict <- [key \in Keys |-> IF \E leaf \in Leaves : key \in keysOf[leaf] 
                                 THEN LET leaf == CHOOSE leaf \in Leaves : key \in keysOf[leaf] 
                                      IN valOf[leaf, key] ELSE MISSING],
         state <- IF state = READY THEN "ready" ELSE "working"


Refinement == Mapping!Spec

\*
\* Invariants
\*
Inners == {n \in Nodes: ~isLeaf[n]}

InnersMustHaveLast == \A n \in Inners : lastOf[n] # NIL
KeyOrderPreserved == \A n \in Inners : (\A k \in keysOf[n] : (\A kc \in keysOf[childOf[n, k]]: kc < k))
LeavesCantHaveLast == \A n \in Leaves : lastOf[n] = NIL
KeysInLeavesAreUnique ==
    \A n1, n2 \in Leaves : ((keysOf[n1] \intersect keysOf[n2]) # {}) => n1=n2
FreeNodesRemain == \E n \in Nodes : IsFree(n)

====