## Implementation Process [0d341ee](https://github.com/tlaplus/Examples/commit/0d341eea047625a85b1967fb64391f18167015d2)
I implemented the EWD998 algorithm based on the TLA+ specification EWD998Chan. The implementation took two hours, during which I did not run or debug the code. Copy-pasting snippets from the specification to the Java code made the translation straightforward, with the exception of developing the low-level network receiver thread, which is abstracted away in the specification.

Disclaimer: [Initially](https://github.com/tlaplus-workshops/ewd998/tree/mku-impl/impl/src/org/kuppe), the code utilized a custom wire format, which I later replaced with JSON to eliminate error-prone ad-hoc parsing.

## [Divergence] Debugging and Error Resolution [2e24bf9](https://github.com/tlaplus/Examples/commit/2e24bf9e20a684df58c37a1d5d5f2ce2eab51a34)
When running the implementation for the first time, I discovered a bug. A node that receives a token must retain the token across the while loop. Resolving this translation error took approximately 15 minutes and required executing the code using a debugger.

## Adding JSON Logging [69f2708](https://github.com/tlaplus/Examples/commit/69f2708c11fbacb2d7a865003d08bd29a60aa391)
In order to add JSON logging, I identified the appropriate places to log where the system is in a consistent state. Logging occurs at two points in the implementation:

1) When a message is received. A message is conceptually received, not when the receiver thread accepts the message from the ServerSocket, but when the message is taken out of the `inbox`. Note that logging in the receiver thread would break the happen-before relationship of some log statements due to multithreading, leading to inconsistencies.
2) When a message is sent.

## Trace Validation [5e0b9f5](https://github.com/tlaplus/Examples/commit/5e0b9f5897b1f9592e881f4fd9c5258c5db4af9f)
The trace validation mapping, as suggested by [Ron Pressler](https://www.youtube.com/watch?v=TP3SY0EUV2A), is not well-suited for validating a trace that is extremely partial. EWD998's trace neither has the values of all variables nor logs every state of the system.

Using non-determinism to axiomatically define the missing values tends to become impractical, as it quickly results in a TLA+ fragment that TLC cannot handle.  For example, consider the following sub-formula of the next-state relation where the first conjunct defines an *infinite* set of functions, from which the second conjunction filters an *infinite* subset:

```tla
SomeSubAction ==
    /\ ...
    /\ inbox' \in [Node -> Seq(Msg)]
    /\ \E idx \in DOMAIN inbox[Initiator]': 
            inbox[Initiator][idx]' = Trace[TLCGet("level")].msg
    /\ ...
```

A constructive definition, on the other hand, is cumbersome and, thus, error-prone in TLA+.  My workaround involves defining TLC *state* and *action constraints* that match each line in the trace to the current state of a prefix of some behavior defined by the *original*, *high-level* specification. A trace is accepted iff TLC can match every line in the trace to the corresponding state in a (prefix of) a  high-level spec behavior.

## Absence of Global Clock [61d6be7](https://github.com/tlaplus/Examples/commit/61d6be787445b7c5b7870b93ecc509cb50413abe)
A fundamental problem of distributed systems is the absence of a global clock, which is why the trace/log file may be causally unordered. For example, the receiver of a message might log the receipt of a message before the sender logs the corresponding send event. The canonical solution in distributed systems is a vector clock, which is modeled in EWD998ChanID to interface with ShiViz (https://bestchai.bitbucket.io/shiviz).

## Updating JSON Logging for ShiViz Compatibility [7897628](https://github.com/tlaplus/Examples/commit/78976282cd7c71345cc042eb73cd2d577cac0277)
I included the node's identity in the JSON logging to ensure compatibility with ShiViz. The following regex was used:

```regex
^{"event":"(<|>|d)","node":(?<host>[0-9]?),"pkt":{("snd":(?<src>[0-9]?),"rcv":(?<rcv>[0-9]?),"msg":(?<event>({"type":"tok","q":-?[0-9]*,"color":"(white|black)"}|{"type":"(pl|trm|w|d)"})),|)"vc":(?<clock>.*)}}
```

## Introducing Stuttering Steps for Token Passing [98c4d40](https://github.com/tlaplus/Examples/commit/98c4d40c31e0fed1d923a6cbddd7cfb593991f51)
In the high-level TLA+ specification EWD998Chan, token passing is modeled as a single atomic step. However, in real-world systems, token passing is not atomic and is transmitted via the network. To address this issue, I introduced explicit stuttering steps, where variables remain unchanged, at the price of the length of the behavior increasing.

## Handling Unlogged Deactivation Events [ad8988f](https://github.com/tlaplus/Examples/commit/ad8988f53c505995343ed049db932740c7116865)
Trace validation faces challenges such as the absence of node deactivation events in the logs, which leads to a rejected trace when a seemingly active node passes the token. The limitations of TLC in supporting the composition of actions (as discussed in section 7.3, pages 76ff, of Lamport's Specifying Systems) hinder the TraceSpec from defining its next-state relation by conjoining `Deactivate \cdot PassToken`. However, this limitation can be overcome by defining a suitable action that deactivates the node when it passes the token.

Related: https://github.com/tlaplus/tlaplus/pull/805

## Improving Trace Validation Coverage [55e9a64](https://github.com/tlaplus/Examples/commit/55e9a645053b8e9b8cf34c95800c85273022bc51)
The previous step demonstrated how manually composed actions can handle missing state changes in the trace or log file, and I see no reason why this approach won't generalize beyond this specific example. In the case of the EWD998 implementation, it is possible to consistently log when a node deactivates, thereby increasing the coverage of trace validation by including more system state.

## [Divergence] Handling Termination Messages in Trace Validation [7f157c8](https://github.com/tlaplus/Examples/commit/7f157c82bf45e54b8d66f16ebce818d98d16b031)
Trace validation starts to reject traces due to the presence of termination ("trm") messages in the implementation, which are not included in the EWD998 model. This discrepancy between the specifications and the actual code could have been easily identified through a manual comparison between the two. To resolve this issue, I define the `TraceNextConstraint` to allow for "trm" messages and base it on finite stuttering, similar to the way the `IsRecvToken` is handled.

## [Divergence] SendMsg Action [ff7a49a](https://github.com/tlaplus/Examples/commit/ff7a49a1012a5b4508cc888a7d9db03d334a9861)
Trace validation detects another divergence between the high-level specification and the implementation. The `SendMsg` action in the high-level specification does not allow a message to be sent from a node to itself. Although self-messaging is safe and does not violate the properties of the specification, I choose to modify the implementation to match the specification more closely.

## [Divergence] Single node configuration [75673c4](https://github.com/tlaplus/Examples/commit/75673c451e9c95f6dc34689e285aebee572a3cdd)
Trace validation identified a divergence between the specification and the code implementation. In a system with only one node, the token does not appear to be moving. To handle this edge case, I have adjusted the `IsInitiateToken` predicate to account for this scenario.

## Logging Exceptions [27d721c](https://github.com/tlaplus/Examples/commit/27d721c5f23f1f64102ce93a8ce1a365947057a8)
In the code implementation, all exceptions are logged as special events in the log file. To maintain consistency with the specification, I have ensured that exceptions are logged to the trace and cause the trace validation to fail.

## [Divergence] Trace Validation Divergence [5665744](https://github.com/tlaplus/Examples/commit/566574473a8ce2d336b7efcf5ec7725809170aae)
Upon performing trace validation, I discovered another divergence after generating approximately 10,000 states within ~30 seconds. The initiator initiates another token round even when the previous token round is conclusive. This issue occurs when the system is in a state with all nodes being white and inactive except for an active, but white, initiator that owns the token.

## [Divergence] Final Implementation [4da7373](https://github.com/tlaplus/Examples/commit/4da7373f9688d252758419f14b0c495e36a61927)
I had to revert the (bogus) bugfix attempt above. To address the issue, I have now implemented the EWD998 specification correctly, ensuring that the divergence is eliminated and the system functions as expected.  Trace validation no longer finds divergences.

--------------

Note to self: Random stuff at /Users/markus/src/TLA/_specs/examples/specifications/ewd998 [mku-TraceValidation]