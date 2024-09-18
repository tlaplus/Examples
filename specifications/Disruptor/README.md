# Disruptor

The Disruptor originates from LMAX Exchange and is a data structure for very low latent communciation between producers and consumer threads using a ring buffer.

The TLA+ models in this folder model an implementation of the Disruptor in Rust.
See [Github](https://github.com/nicholassm/disruptor-rs) for the Rust implementation and [LMAX's Github page](https://github.com/LMAX-Exchange) for the original Disruptor implemented in Java.

This folder contains two models for verifying the Single Producer Multi Consumer (SPMC) and Multi Producer Multi Consumer (MPMC) scenarios.

The reason for modelling the Disruptor is to verify that there are no data races between producers and consumers which is not trivial to realise.

