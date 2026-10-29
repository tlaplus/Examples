# Specification Refinement

This example accompanies Hillel Wayne's blog post [*Specification Refinement*](https://www.hillelwayne.com/post/refinement/), which introduces refinement mappings in TLA⁺ using a two-thread counter:

- [`abstract.tla`](abstract.tla) (`abstract.cfg`): The high-level specification where two threads atomically increment a shared `counter` and transition from `"start"` to `"done"`.
- [`bad.tla`](bad.tla) (`bad.cfg`): A lower-level specification that splits the increment into two non-atomic steps (`GetCounter` and `IncCounter`) using a thread-local variable `tmp` and an intermediate state `"inc"`. Checking `PROPERTY Refinement` with TLC fails with a liveness/temporal property violation, exhibiting the race condition where both threads read `0` and both write `1`.
- [`good.tla`](good.tla) (`good.cfg`): Adds a `lock` variable to make the read-modify-write critical section mutually exclusive. TLC verifies that `good` refines both `abstract` (`Refinement`) and `bad` (`RefinesBad`).
- [`good_proof.tla`](good_proof.tla): TLAPS machine-checked proofs that `good` refines both `abstract` (`THEOREM ImplementsAbstract == Spec => Refinement`) and `bad` (`THEOREM ImplementsBad == Spec => RefinesBad`).
