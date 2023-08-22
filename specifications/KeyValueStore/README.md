This repo contains TLA+ specifications of  simple key-value store exhibiting snapshot algorithm. 

## TLA+ model 
Andrew Helwer contributed the following:
+ `KeyValueStore.tla` has the TLA+ specs for the key-value store with snapshot isolation
+ `MCKS.tla` is the file to use for TLC model checking
+ `MCKVS*.cfg` are alternative config files to use for TLC checking


## PlusCal model
Murat Demirbas wrote a PlusCal version of the key-value store with snapshot isolation. He also instantiated the `ClientCentric.tla` (from Tim Soethout's work) to be able to properly check the key-value store for snapshot isolation semantics. 
+ `KVsnap.tla` is the Pluscal model for the key-value store
+ `MCKVsnap.tla` is the file to use for TLC model checking
+ `MCKVsnap.cfg` is the corresponding config file for model checking (with this config, model checking completes under a minute; it is possible to add another key and model check)

If you uncomment the Serialization invariant in `KVsnap.tla`, and `MCKVsnap.cfg`, you can see a counterexample of how this snapshot-isolation key-value store violates serializability.

## Model checking with VSCode TLA+ plugin
+ Make sure TLA+ plugin is installed in VSCode
+ Open the .cfg file you are interested in checking in VSCode 
+ Get the VSCode panel (Option+X on Mac), and choose "TLA+: Check Model with TLC") 