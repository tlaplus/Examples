# Wrangling monotonic systems in TLA⁺: Tractable modeling of replicated logs & CRDTs
*This blog post is licensed under [CC-BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
Originally published by Andrew Helwer at https://ahelwer.ca/post/2023-11-01-tla-finite-monotonic/ on 2023-11-01.*

TLA⁺ sees a lot of use modeling distributed systems.
The ability to explore all possible interleavings of events makes concurrency simple to reason about.
For this TLA⁺ uses something called finite model-checking, which is really just a breadth-first search through the entire state space.
The key here - and this really must be emphasized - is that the model is *finite*.
There can't be an infinite number of states, or of course the model checker will run forever.

Unfortunately, a lot of distributed systems are designed with infinitely-expanding state at their core.
You want your system to be *monotonic*, which means it never revisits an earlier state.
This is because ordering things in a distributed system is very difficult.
If your system always progresses through states, never returning to earlier ones, it gives you a simple way to order your system and say it was in one state before it was in another state.
A whole class of problems evaporate.

Here is an example: a number that only increases in value, which we'll call a monotonic counter.
Monotonic counters are used everywhere in distributed systems.
In fact, I struggle to think of a distributed system that *doesn't* have a monotonic counter somewhere in its design.
Here's a short list of ways I've seen monotonic counters used:
 * transaction IDs
 * live configuration versioning
 * indices in an append-only log
 * proposal ballot numbers in consensus algorithms

So here's the problem: we want to subject distributed systems to finite modeling, but they try to cram as much infinity as possible into their system designs.
How do we square this circle?

## The hammer: state restrictions

Here's a method long used by many TLA⁺ practitioners, including myself.
Just pick an arbitrary point and say "okay, we've explored enough of the state space, don't go beyond here".
So your monotonic counters are limited to, say, 10 or below.
If you haven't found a bug by the time your counter hits 10 it probably doesn't exist, so the thinking goes.
This is actually pretty good thinking!
Indeed, when designing a model you're often making tradeoffs between state exploration and your model finishing before the heat death of the universe.
It's rare, for example, for a TLA⁺ model to use more than three nodes in a distributed system despite production systems often involving many, many more nodes than that.
TLA⁺ is still extraordinarily effective at finding bugs in these models, which is a testament to the complexity of concurrent & distributed systems generally.
Us programmers can barely think straight about one computer, let alone three or more!

Unfortunately, if you add state restrictions you've cut yourself off from many powerful TLA⁺ features (see page 247, section 14.3.5 of [*Specifying Systems*](https://lamport.azurewebsites.net/tla/book.html) for details).
In particular, you'll lose the ability to analyze liveness (good things eventually happen) or abstraction & refinement (showing that one spec is related to another).
Sometimes this is a decent tradeoff, because safety checking (bad things don't happen) can still be used and is often all the system needs.
Still, is there a technique to get the best of both worlds?

## Lamport's abstraction

In his 2005 paper *Real Time is Really Simple* ([pdf](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-30.pdf)), Leslie Lamport faced a similar problem modeling real-time systems in TLA⁺.
Real-time systems have all sorts of restrictions like "this process must complete before this time" and "this process can only start after this time".
It's interesting to think about how to model this.
A simple approach could have a single variable called `clock` or `now` which monotonically increases as time passes (say, measuring seconds elapsed), and there are timers associated with specific future values of that variable.
These timers function as either deadlines or triggers for events.

Lamport's core insight was that the specific value of this clock variable *cannot matter*.
How could it?
What would it start at?
Would it start at 0 as the system comes online?
Would it be initialized to [Unix time](https://en.wikipedia.org/wiki/Unix_time)?
Why not the Gregorian calendar, or even the Mayan calendar?
The system would obviously function identically in all of these schemes.
All that matters, he concluded, is how far away all our timers are from the present moment.
So when time passes, we don't update the clock: we update the timers!

This translates very well to a finite model.
Instead of having an infinite monotonically-increasing clock, we just have a collection of timer variables whose values are restricted to some small quantity.
These timers might be initialized to some value, but they only ever spiral down toward zero.
The infinite rendered finite.
We will apply this insight to all of our monotonic systems.

## Constraining divergence

It's time to put our thinking caps on and consider carefully what we actually want to model with these monotonic counters.
I argue we *really* just want to capture divergence.
All the interesting behavior in distributed systems occurs when the different nodes have a different view of what's true, usually caused by some of them lagging behind others in receiving & processing updates.
Suppose you have a three node system, where each node has its view of the current value of some monotonic counter.
Is there really any difference between those nodes believing the value is `1`, `2`, and `3` respectively, as opposed to `101`, `102`, and `103`?
I argue there is not.
We can think of these counters as analogous to the clock from up above: all we care about is the difference between the highest value believed to be true and the lowest value.
We call this difference the divergence.
Thus, normalize: when all the counters on all the nodes reach some nonzero value, transpose them so the lowest value is zero.
We will call this operation garbage collection.

We want to constrain divergence to a finite value.
Here we see a classic tradeoff between expressivity and tractability: the larger the divergence limit, the larger our state space and thus the greater our possibility of generating interesting behavior that triggers bugs, but also the longer our model will run.
What happens when a node tries to increment its counter beyond our divergence limit?
Simple, we don't let it.
Other nodes will need to catch up a bit and then all the counters will have to be garbage-collected to open up some space for additional incrementing.

One might object that this is all a bit artificial: real systems don't have this monotonic counter garbage collection process, and they certainly don't keep nodes from progressing just because some other node is frozen.
I contend this is necessary and part of the art of abstracting a system to model what is really interesting about it.
We don't care about the actual values of these counters.
We only care about their divergence, and this is how you model divergence without resorting to the state restriction hammer.
As we'll see, we can also neatly separate these artificial aspects from the spec itself, so as not to distract readers with irrelevant detail.

## Modeling a conflict-free replicated data type

Let's take the quintessential monotonic eventually-consistent distributed system, a grow-only counter [CRDT](https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type).
With a grow-only counter, you have a network of nodes keeping track of some increasing quantity - say, the number of requests they service.
Each node holds a vector of counters, and a node is associated with a specific index in that vector.
When a node services a request, it increments only its index in its vector.
Occasionally, the nodes will gossip their entire vector to each other, and the recipient merges the vector with their own by taking the max of each element.
Thus the total number of requests serviced by the system is found by summing all the elements of the vector on any given node, although the result might differ & lag slightly between nodes.
Here's how we write this in TLA⁺:
```tla
------------------------------- MODULE CRDT ---------------------------------
EXTENDS Naturals

CONSTANT Node

VARIABLE counter

TypeOK ≜ counter ∈ [Node → [Node → ℕ]]

Init ≜ counter = [n ∈ Node ↦ [o ∈ Node ↦ 0]]

Increment(n) ≜ counter' = [counter EXCEPT ![n][n] = @ + 1]

Gossip(n, o) ≜
  LET Max(a, b) ≜ IF a > b THEN a ELSE b IN
  counter' = [
    counter EXCEPT ![o] = [
      nodeView ∈ Node ↦
        Max(counter[n][nodeView], counter[o][nodeView])
      ]
    ]

Next ≜
  ∨ ∃ n ∈ Node : Increment(n)
  ∨ ∃ n, o ∈ Node : Gossip(n, o)

Spec ≜
  ∧ Init
  ∧ □[Next]_counter

=============================================================================
```
**Note**: *All TLA⁺ snippets in this post use the unicode format.
Convert them to their ASCII equivalents (and vice-versa) using [tlauc](https://github.com/tlaplus-community/tlauc).*

What things do we want to verify about this system?
Here's a safety check we could add, just to make sure we modeled the system correctly: a node will always have the highest value of its own counter among all other nodes:
```tla
Safety ≜ ∀ n, o ∈ Node : counter[n][n] ≥ counter[o][n]
```
We also will want to validate that the system is monotonic.
In TLA⁺ we do this by saying every single step ensures all the values in the  `counter` variable are greater than or equal to their previous values:
```tla
Monotonic ≜ ∀ n, o ∈ Node : counter'[n][o] ≥ counter[n][o]
Monotonicity ≜ □[Monotonic]_counter
```
Finally, the big one: this is an eventually-consistent system, so we want to validate its eventual consistency as a liveness property!
We want to say it is always the case that eventually the vectors on all nodes will have the same value.
Let's define this goal state as:
```tla
Convergence ≜ ∀ n, o ∈ Node : counter[n] = counter[o]
```
While we want to say this property will always eventually be true in our system, that isn't actually correct!
Think of a system servicing huge numbers of requests, far more often than it gossips vectors to the other nodes.
Such a system will always have its vectors slightly out of date, and so convergence never happens.
Really our convergence property will only become true if all requests stop for a while.

We model this by adding a boolean variable, `converge`, which is arbitrarily set to `TRUE` at some point and stops additional increments from occurring.
Since this is a virtual variable that wouldn't exist in any real system, we should move it out into a model-checking spec that imports our "good copy" spec and wraps its definitions with `converge` logic:
```tla
------------------------------ MODULE MC_CRDT -------------------------------
CONSTANT Node

VARIABLES counter, converge

vars ≜ ⟨counter, converge⟩

S ≜ INSTANCE CRDT

TypeOK ≜
  ∧ S!TypeOK
  ∧ converge ∈ BOOLEAN

Safety ≜ S!Safety

Monotonicity ≜ S!Monotonicity

Liveness ≜ converge ↝ S!Convergence

Init ≜
  ∧ S!Init
  ∧ converge = FALSE

Increment(n) ≜
  ∧ ¬converge
  ∧ S!Increment(n)
  ∧ UNCHANGED converge

Gossip(n, o) ≜
  ∧ S!Gossip(n, o)
  ∧ UNCHANGED converge

Converge ≜
  ∧ converge' = TRUE
  ∧ UNCHANGED counter

Next ≜
  ∨ ∃ n ∈ Node : Increment(n)
  ∨ ∃ n, o ∈ Node : Gossip(n, o)
  ∨ Converge

Fairness ≜ ∀ n, o ∈ Node : WF_vars(Gossip(n, o))

Spec ≜
  ∧ Init
  ∧ □[Next]_vars
  ∧ Fairness

=============================================================================
```
Of note is our new `Liveness` property, which states `converge` being true *leads to* (`↝`) our convergence condition:
```tla
Liveness ≜ converge ↝ S!Convergence
```
We also require an additional *fairness assumption* to satisfy this property, which states `Gossip` operations must actually happen and the system can't just obstinately sit doing nothing forever:
```tla
Fairness ≜ ∀ n, o ∈ Node : WF_vars(Gossip(n, o))
```
At this point we have to consider how to actually manage the (currently infinite) state of the model.
We can run the modelchecker if we want, with this configuration:
```sh
SPECIFICATION Spec
CONSTANT Node = {n1, n2, n3}
INVARIANTS TypeOK Safety
PROPERTIES Liveness Monotonicity
```
It will of course run forever.

We can quickly define a state restriction in `MC_CRDT`:
```tla
StateConstraint ≜ ∀ n, o ∈ Node : counter[n][o] ≤ 3
```
Then use this configuration:
```sh
SPECIFICATION Spec
CONSTANT Node = {n1, n2, n3}
INVARIANTS TypeOK Safety
PROPERTIES Liveness Monotonicity
CONSTRAINT StateConstraint
```
The modelchecker will find 50,000 states and validates our `TypeOK` & `Safety` invariants against all of them (yay!), but silently ignores the `Liveness` and `Monotonicity` properties due to the inclusion of the state constraint.
Here we have to deploy the technique we developed up above: constraining divergence & using garbage collection.
We add a new `Divergence` constant and a `GarbageCollect` action:
```tla
------------------------------- MODULE MC_CRDT ------------------------------
EXTENDS Naturals

CONSTANTS Node, Divergence

VARIABLES counter, converge

vars ≜ ⟨counter, converge⟩

S ≜ INSTANCE CRDT

TypeOK ≜
  ∧ S!TypeOK
  ∧ counter ∈ [Node → [Node → 0 ‥ Divergence]]
  ∧ converge ∈ BOOLEAN

Safety ≜ S!Safety

Monotonicity ≜ S!Monotonicity

Liveness ≜ converge ⇒ S!Liveness

Init ≜
  ∧ S!Init
  ∧ converge = FALSE

Increment(n) ≜
  ∧ ¬converge
  ∧ counter[n][n] < Divergence
  ∧ S!Increment(n)
  ∧ UNCHANGED converge

Gossip(n, o) ≜
  ∧ S!Gossip(n, o)
  ∧ UNCHANGED converge

Converge ≜
  ∧ converge' = TRUE
  ∧ UNCHANGED counter

GarbageCollect ≜
  LET SetMin(s) ≜ CHOOSE e ∈ s : ∀ o ∈ s : e ≤ o IN
  LET Transpose ≜ SetMin({counter[n][o] : n, o ∈ Node}) IN
  ∧ counter' = [
      n ∈ Node ↦ [
        o ∈ Node ↦ counter[n][o] - Transpose
      ]
    ]
  ∧ UNCHANGED converge

Next ≜
  ∨ ∃ n ∈ Node : Increment(n)
  ∨ ∃ n, o ∈ Node : Gossip(n, o)
  ∨ Converge
  ∨ GarbageCollect

Fairness ≜ ∀ n, o ∈ Node : WF_vars(Gossip(n, o))

Spec ≜
  ∧ Init
  ∧ □[Next]_vars
  ∧ Fairness

=============================================================================
```
Note in the `Increment` action we have:
```tla
  ∧ counter[n][n] < Divergence
```
preventing any individual counter from exceeding our divergence constraint.
The `GarbageCollect` action finds a counter value exceeded by every counter on every node, and subtracts it from all of them to transpose the counters closer to zero.

We're ready!
We can run the model with this configuration:
```sh
SPECIFICATION Spec
CONSTANTS
  Node = {n1, n2, n3}
  Divergence = 3
INVARIANTS TypeOK Safety
PROPERTY Liveness
```
Once again the modelchecker finds 50,000 states, but this time it can actually run the liveness checking!
Our `Safety` invariant passes like before, but this time our `Liveness` property passes as well!
So our system is shown to converge as hoped.

Unfortunately, our `Monotonicity` property doesn't fare as well.
If we check:
```sh
PROPERTIES Liveness Monotonicity
```
We see that `Monotonicity` fails to hold whenever a `GarbageCollect` step occurs, which is unsurprising.
Recall the statement of `Monotonicity`:
```tla
Monotonic ≜ ∀ n, o ∈ Node : counter'[n][o] ≥ counter[n][o]
Monotonicity ≜ □[Monotonic]_counter
```
Since `GarbageCollect` decreases the values of all the elements of `counter`, this is clearly violated.
How can we rescue the concept of monotonicity here?
Transposition maintains the *relative* values of the counters, despite their absolute values changing.
Another way to say this is that every counter changes by the same amount:
```tla
Monotonicity ≜ □[
  ∨ S!Monotonic
  ∨ ∀ a, b, c, d ∈ Node :
    (counter'[a][b] - counter[a][b]) = (counter'[c][d] - counter[c][d])
]_vars
```
This passes!
We have now completed a demonstrative example of modelchecking a monotonic system.
This approach can be applied to any other monotonic system.
We can tune the divergence constraint to trade off between state exploration and ease of modelchecking; in our model of three nodes, this looks like:

| Divergence | Distinct States | Modelcheck Time |
|------------|-----------------|-----------------|
| 1          | 264             | <1s             |
| 2          | 5232            | 1s              |
| 3          | 50,000          | 7s              |
| 4          | 300,750         | 50s             |
| 5          | 1,335,642       | 4m20s           |

By comparison keeping divergence at 3 but increasing the number of nodes to 4 scales the state space much faster: it hit 20 million distinct states before I killed the process after about an hour.
It's possible to use symmetry reduction to collapse the number of states introduced by nodes, but you can see why most models only use three nodes!
The combinatorial state explosion is real.

## Modeling a replicated log

I'll here sketch a similar tactic for modeling a replicated log.
Replicated logs have transactions appended to them, growing forever.
Not only that, they're brutal to modelcheck: since every action is recorded in the log, states gain path dependence.
If action `A` occurs before action `B`, and it leads to the same outward system state as if `B` occurs before `A`, the modelchecker will nonetheless treat these as separate states because the order of `A` and `B` was recorded in the log.
This gives *factorial* state explosion, restricting us to very short logs.
In some systems this is barely enough to get things initialized, let alone explore interesting behavior.

Our approach can help with both problems.
Remember we only care about restricting divergence: here, that means divergence of how far behind a node is in executing log transactions.
Nodes in the cluster process the log at different rates, and some can lag behind others.
As before this causes a lot of interesting behavior.
If we limit this divergence, then nodes can't add additional transactions to the log if that would push a node outside the execution divergence limit.
On the other end, our garbage collection step will remove transactions from the beginning of the log once all nodes have executed them.
Easy!

[According to A. Jesse Jiryu Davis of MongoDB](https://groups.google.com/g/tlaplus/c/3V1JxNDSoas/m/3Y81pxi2AQAJ), this approach is similar to how some real-world replicated logs work (although usually the lagging nodes are kicked out instead of execution being paused).
A nice bonus.
You can find an example replicated log spec (and the CRDT spec from up above) [here](https://github.com/ahelwer/Examples/tree/057148b2fc8cdb21914fb3ba840681c22cf8c0f3/specifications/FiniteMonotonic).

## Alternatives & future work

This post didn't even touch the built-in TLA⁺ proof language, which might have found use here.
Infinity is not an obstacle to mathematical induction!
There are also alternative state representations which could have been used, to tighten the analogy to Lamport's *Real Time* approach.
Instead of a garbage collection step resetting the state, the specs could have been rewritten to track state divergence explicitly.
Another way of saying this is garbage collection could be built in to the CRDT model's `Gossip` step: the counters are normalized at the end of it.
This might have been more elegant, potentially at the cost of making the spec harder to understand.
It certainly would improve modelcheck time by reducing extraneous state transitions.

I had previously written a spec of a real-world replicated log system (detailed in a [past post](/post/2023-04-05-checkpoint-coordination/)) that used the state restriction method to curtail infinity.
It would be nice to go back and apply our new approach to an existing spec, not greenfield demonstration projects as in this post.
Perhaps you'll see an update in a few months!

I also have an upcoming industry contract to specify a database system that includes both monotonic counters and replicated logs, and I'm excited to see how this new approach pans out.
If you'd like to hire me for a similar contract, contact consulting@disjunctive.llc!

## Discussions

 * [lobste.rs](https://lobste.rs/s/mo4epa/wrangling_monotonic_systems_tla)
 * [fediverse](https://fosstodon.org/@ahelwer/111336831792925594)
 * [TLA⁺ mailing list](https://groups.google.com/g/tlaplus/c/3V1JxNDSoas/m/ffHjY1VwFgAJ)
 * [Hacker News](https://news.ycombinator.com/item?id=38103225)
 * [LinkedIn](https://www.linkedin.com/posts/ahelwer_wrangling-monotonic-systems-in-tla-activity-7125557738771779584-Xwv3)

