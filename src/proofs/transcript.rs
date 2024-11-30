//! Defines a `TranscriptProtocol` trait for using a Merlin transcript.

use curv::{arithmetic::{Converter, Modulo}, elliptic::curves::{Point, Scalar, Secp256k1}, BigInt};
use merlin::Transcript;

pub trait TranscriptProtocol {
    /// Append a domain separator for an `n`-party, `b` and `b_bar`-bit range proof.
    fn varrange_domain_sep(&mut self, n: u64, b: u64, b_bar: u64);

    /// Append a domain separator for a length-`n` inner product argument.
    fn ipa_domain_sep(&mut self, n: u64);

    /// Append a domain separator for a length-`n` sigma protocol for pedersen commitment.
    fn sigma_pedersen_domain_sep(&mut self, n: u64);

    /// Append a `scalar` with the given `label`.
    fn append_scalar(&mut self, label: &'static [u8], scalar: &Scalar<Secp256k1>);

    /// Append a `point` with the given `label`.
    fn append_point(&mut self, label: &'static [u8], point: &Point<Secp256k1>);

    /// Append `points` with the given `label`.
    fn append_points_array(&mut self, label: &'static [u8], points: &[Point<Secp256k1>]);

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar<Secp256k1>;
}

impl TranscriptProtocol for Transcript {
    fn varrange_domain_sep(&mut self, n: u64, b: u64, b_bar: u64) {
        self.append_message(b"dom-sep", b"varrange v1");
        self.append_u64(b"n", n);
        self.append_u64(b"b", b);
        self.append_u64(b"b_bar", b_bar);
    }

    fn ipa_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"ipa v1");
        self.append_u64(b"n", n);
    }

    fn sigma_pedersen_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"sigma_pedersen v1");
        self.append_u64(b"n", n);
    }

    fn append_scalar(&mut self, label: &'static [u8], scalar: &Scalar<Secp256k1>) {
        self.append_message(label, &scalar.to_bigint().to_bytes());
    }

    fn append_point(&mut self, label: &'static [u8], point: &Point<Secp256k1>) {
        self.append_message(label, &point.to_bytes(false)[..]);
    }

    fn append_points_array(&mut self, label: &'static [u8], points: &[Point<Secp256k1>]) {
        let points = points.to_vec();
        for j in 0..points.len() {
            self.append_point(label, &points[j]);
        }
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> Scalar<Secp256k1> {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);
        
        let order = Scalar::<Secp256k1>::group_order();
        let bn = BigInt::from_bytes(&buf);
        Scalar::<Secp256k1>::from_bigint(&BigInt::modulus(&bn, &order))
    }
}
