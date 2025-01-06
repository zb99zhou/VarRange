# VarRange: an aggregated range proof supporting different bases and ranges.

This repository provides an implementation of VarRange, an aggregated range proof that supports different bases and ranges.

An aggregated range proof allows a single prover to prove that multiple committed values lie within specified ranges simultaneously. Given $n$ Pedersen commitments with different commitment keys, VarRange proves that each committed value lies within its respective range.

## Tests

Run tests using  `cargo test --release`.