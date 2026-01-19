----------------------------- MODULE Digraph -----------------------------

(**************************************************************************************)
(* A digraph is a pair consisting of a set of vertices and a set of edges             *)
(**************************************************************************************)
 
Vertices(digraph) == digraph[1]
Edges(digraph) == digraph[2]

IsDigraph(digraph) ==
    /\  digraph = <<Vertices(digraph), Edges(digraph)>>
    /\  \A e \in Edges(digraph) :
        /\  e = <<e[1],e[2]>>
        /\  {e[1],e[2]} \subseteq Vertices(digraph)

Children(digraph, v) ==
    {c \in Vertices(digraph) : <<v, c>> \in Edges(digraph)}

(**************************************************************************************)
(* Descendants(dag, vs) is the set of vertices reachable from any vertex in vs       *)
(**************************************************************************************)
RECURSIVE Descendants(_, _)
Descendants(dag, vs) == IF vs = {} THEN {} ELSE
    LET children == {c \in Vertices(dag) : \E v \in vs : <<v,c>> \in Edges(dag)} IN
        children \cup Descendants(dag, children)

(**************************************************************************************)
(* The sub-dag reachable from the set of vertices vs:                                 *)
(**************************************************************************************)
SubDag(dag, vs) ==
    LET vs2 == Descendants(dag, vs) \cup vs
        es2 == {e \in Edges(dag) : e[1] \in vs2} \* implies e[2] \in vs2
    IN  <<vs2, es2>>
    
==========================================================================
