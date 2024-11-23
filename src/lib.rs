#![allow(clippy::many_single_char_names, clippy::too_many_arguments)]

extern crate serde_derive;
extern crate serde;

extern crate curv;
extern crate generic_array;
extern crate itertools;
extern crate sha2;

pub mod proofs;

#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum Errors {
    InnerProductError,
    RangeProofError,
    SigmaPedersenProofError,
    VarRangeError
}