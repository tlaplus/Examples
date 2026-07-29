----------------------- MODULE MCFlashWithMutexLive -----------------------
EXTENDS FlashWithMutex

\* Deliberately no Symmetry definition: TLC's symmetry reduction can miss
\* liveness violations, so the liveness model explores the unreduced graph.
\* Safety and the Murphi Lemma_* invariants are checked, with symmetry, by
\* MCFlashWithMutex.cfg instead.

==============================================================================
