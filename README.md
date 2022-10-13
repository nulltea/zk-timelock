# <p align="center"> zk-timelock </p>
This repo contains arithmetic circuits for verifiable time-lock encryption made using [arkworks-rs](https://github.com/arkworks-rs) toolkit. For more details on such an encryption scheme see [`drand/tlock`](https://github.com/drand/tlock) (Go) and [`timoth-y/tlock-rs`](https://github.com/timoth-y/tlock-rs) (Rust) repos.

## Overview
The algorithm implemented here is the Boneh-Franklin's [\[1\]](https://crypto.stanford.edu/~dabo/papers/bfibe.pdf) identity-based encryption (IBE) (see Rust code [here](https://github.com/timoth-y/tlock-rs/blob/main/tlock/src/ibe.rs#L19)). The main challenge with translating this scheme into an arithmetic circuit comes from the heavy use of target group (pairing product) operations, specifically `gt` on `fr` multiplication.

All operations must be projected on top of the BLS12-381, as this is the only curve currently supported by the [drand](https://drand.love/) threshold network. This poses a problem as there is no commonly known pairing-friendly curve whose scalar field equals the base field of BLS12-381, which is needed for efficient KZG-based SNARKs.

There are multiple ways to tackle mentioned problems:
1. Change projective curve (e.g. BLS12-377 [\[2\]](https://eprint.iacr.org/2018/962) that can be embedded into BW6-761 [\[3\]](https://eprint.iacr.org/2020/351))
    - trade-off: requires changes to the drand protocol.
2. Simulate BLS12-381 using non-native arithmetic
    - trade-off: huge performance overhead.
3. Find an application-specific curve that could embed BLS12-381 base field
    - trade-off: such curves would have low FFT space, but we can leverage Gemini [\[4\]](https://eprint.iacr.org/2022/420) proving system to handle such brittle fields.
4. Use [Halo2](https://github.com/zcash/halo2) proving system that defers all the pairings to the very end (i.e. accumulators), this makes nonnative operations cheaper
    - trade-off: dev tools to construct a halo2 circuit are currently lacking.

For the sake of experiments, this repo provides circuits for the first three approaches. For the third approach, it also introduces [`YT6-776`](./src/yt6_776) - an application-specific curve that embeds BLS12-381's base field. See details about it [here](./src/yt6_776).

## Circuits
- [`Circuit<E: Pairing, P: Bls12Parameters>`](https://github.com/timoth-y/zk-timelock/blob/main/src/circuits.rs#L41): a generic-curve circuit with native arithmetic only. Can be proved using the Groth16 system with BLS12-377/BW6-671 curve combination.
- [`NonnativeCircuit<C: CurveGroup>`](https://github.com/timoth-y/zk-timelock/blob/main/src/circuits.rs#L327): a circuit that simulates BLS12-381 base fields using non-native arithmetic. Can be proved by using the Groth16 system with any projective/pairing curves combination (also BLS12-377/BW6-671 here.
- [`GeminiNativeCircuit`](https://github.com/timoth-y/zk-timelock/blob/main/src/circuits.rs#L327): a modified native that (currently) comes without input variables (see [this issue](https://github.com/arkworks-rs/gemini/issues/5) for details). Can be proved using the Gemini system with a BLS12-381/YT6-776 curve combination.

## Benchmarks
The experimental results can be found on [BENCHMARKS.md](./BENCHMARKS.md).

## Usage
To perform benchmarks on your machine run `cargo bench` command.

For examples of each circuit usage see [`benches/ibe_benchmark.rs`](https://github.com/timoth-y/zk-timelock/blob/main/benches/ibe_benchmark.rs).

## Acknowledgements
I greatly thank [Weikeng Chen](https://github.com/weikengchen) for sharing method of creating application-specific curves [\[5\]](https://eprint.iacr.org/2022/1145.pdf) and all the helpful discussions about it.

## References
- \[1\] Identity-Based Encryption from the Weil Pairing https://crypto.stanford.edu/~dabo/papers/bfibe.pdf
- \[2\] Zexe: Enabling Decentralized Private Computation https://eprint.iacr.org/2018/962
- \[3\] Optimized and secure pairing-friendly elliptic curves suitable for one layer proof composition https://eprint.iacr.org/2020/351
- \[4\] Gemini: Elastic SNARKs for Diverse Environments https://eprint.iacr.org/2022/420
- \[5\] YAFA-108/146: Implementing Ed25519-Embedding Cocks-Pinch Curves in Arkworks-rs https://eprint.iacr.org/2022/1145.pdf
