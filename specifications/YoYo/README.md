# Yo-Yo leader election algorithm

A TLA+ specification of a leader election algorithm in connected undirected
graphs introduced by Nicola Santoro in chapter 3.8.3 of [Design and Analysis
of Distributed Algorithms](https://research.nicola-santoro.com/DADA.html),
see also [Wikipedia](https://en.wikipedia.org/wiki/Yo-yo_(algorithm)).
The algorithm assumes that every node has a unique (integer) identity and
works by orienting edges of the graph such that sources (nodes with only
outgoing edges) correspond to candidates. It will then successively
execute rounds consisting of two phases edge that serve to
eliminate sources (and reorient edges) until only the node with the
smallest identity remains a source and is a leader.

The module YoYoNoPruning contains the specification of the base algorithm.
It stabilizes in a state where the graph contains a single source, but
does not terminate, since no node can detect stabilization. The module
MCYoYoNoPruning instatiates the algorithm for model checking a number
of properties using TLC.

The module YoYoPruning adds a pruning step to the second phase of each
round in order to remove useless edges and nodes of the graph until the
only source becomes isolated and declares itself the leader, whereas
all other nodes have become inactive. The module MCYoYoPruning serves
for checking properties of this specification using TLC.

The module YoYoAllGraphs describes the same algorithm as YoYoPruning
but performs it on all connected undirected graphs of a certain number
of nodes specified as a parameter. It allows for the algorithm to be
verified beyond a single fixed graph.

The modules depend on the community module UndirectedGraphs for
checking connectedness of the graph.
