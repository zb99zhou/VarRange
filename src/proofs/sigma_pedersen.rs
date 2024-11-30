#![allow(non_snake_case)]

use curv::elliptic::curves::{Point, Scalar, Secp256k1};
use merlin::Transcript;
use crate::{proofs::transcript::TranscriptProtocol, Errors::SigmaPedersenProofError};
use crate::Errors;

pub struct SigmaPedersenProof {
    pub(super) R_vec: Vec<Point<Secp256k1>>,
    pub(super) a_vec: Vec<Scalar<Secp256k1>>,
    pub(super) b_vec: Vec<Scalar<Secp256k1>>
}

impl SigmaPedersenProof {
    pub fn prove(
        transcript: &mut Transcript,
        v_vec: &[Scalar<Secp256k1>],
        x_vec: &[Scalar<Secp256k1>],
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        B_vec: &[Point<Secp256k1>],
        n: usize
    ) -> SigmaPedersenProof {
        assert_eq!(v_vec.len(), n);
        assert_eq!(x_vec.len(), n);
        assert_eq!(g_vec.len(), n);
        assert_eq!(h_vec.len(), n);

        transcript.sigma_pedersen_domain_sep(n as u64);
        transcript.append_points_array(b"B_vec", B_vec);

        let v_vec = v_vec.to_vec();
        let x_vec = x_vec.to_vec();
        let g_vec = g_vec.to_vec();
        let h_vec = h_vec.to_vec();

        transcript.append_points_array(b"g_vec", &g_vec);
        transcript.append_points_array(b"h_vec", &h_vec);

        let mut r_vec: Vec<Scalar<Secp256k1>> = Vec::with_capacity(n);
        let mut s_vec: Vec<Scalar<Secp256k1>> = Vec::with_capacity(n);
        for _j in 0..n {
            r_vec.push(Scalar::<Secp256k1>::random());
            s_vec.push(Scalar::<Secp256k1>::random());
        }

        let R_vec = (0..n)
            .map(|i| &g_vec[i].clone() * r_vec[i].clone() + &h_vec[i].clone() * s_vec[i].clone())
            .collect::<Vec<Point<Secp256k1>>>();

        transcript.append_points_array(b"R_vec", &R_vec);

        let challenge_e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");

        let a_vec = (0..n)
            .map(|i| r_vec[i].clone() + challenge_e.clone() * v_vec[i].clone())
            .collect::<Vec<Scalar<Secp256k1>>>();
        let b_vec = (0..n)
            .map(|i| s_vec[i].clone() + challenge_e.clone() * x_vec[i].clone())
            .collect::<Vec<Scalar<Secp256k1>>>();

        SigmaPedersenProof {
            R_vec,
            a_vec,
            b_vec
        }
    }

    pub fn verify(
        &self,
        transcript: &mut Transcript,
        B_vec: &[Point<Secp256k1>],
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        n: usize
    ) -> Result<(), Errors> {
        assert_eq!(B_vec.len(), n);
        assert_eq!(g_vec.len(), n);
        assert_eq!(h_vec.len(), n);
        assert_eq!(self.R_vec.len(), n);
        assert_eq!(self.a_vec.len(), n);
        assert_eq!(self.b_vec.len(), n);

        transcript.sigma_pedersen_domain_sep(n as u64);
        transcript.append_points_array(b"B_vec", B_vec);

        let B_vec = B_vec.to_vec();
        let g_vec = g_vec.to_vec();
        let h_vec = h_vec.to_vec();

        transcript.append_points_array(b"g_vec", &g_vec);
        transcript.append_points_array(b"h_vec", &h_vec);

        transcript.append_points_array(b"R_vec", &self.R_vec);

        let challenge_e: Scalar<Secp256k1> = transcript.challenge_scalar(b"e");
        let mut flag = true;
        for j in 0..n {
            if &g_vec[j].clone() * self.a_vec[j].clone() + &h_vec[j].clone() * self.b_vec[j].clone() != self.R_vec[j].clone() + challenge_e.clone() * B_vec[j].clone() {
                flag = false;
                break;
            }
        }

        if flag {
            Ok(())
        } else {
            Err(SigmaPedersenProofError)
        }
    }
}

#[cfg(test)]

mod test {
    use curv::{arithmetic::Converter, cryptographic_primitives::hashing::DigestExt, elliptic::curves::{Point, Scalar, Secp256k1}, BigInt};
    use merlin::Transcript;
    use sha2::{Digest, Sha512};

    use crate::proofs::varrange::generate_random_point;

    use super::SigmaPedersenProof;

    pub fn test_helper(seed: &BigInt, n: usize) {
        let g_vec = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to g_vec:
        let h_vec = (0..n)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + seed;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let v_vec: Vec<Scalar<Secp256k1>> = (0..n)
            .map(|_| {
                let rand = Scalar::<Secp256k1>::random();
                rand
            })
            .collect();

        let x_vec: Vec<Scalar<Secp256k1>> = (0..n)
            .map(|_| {
                let rand = Scalar::<Secp256k1>::random();
                rand
            })
            .collect();

        let B_vec = (0..n)
            .map(|i| &g_vec[i].clone() * v_vec[i].clone() + &h_vec[i].clone() * x_vec[i].clone())
            .collect::<Vec<Point<Secp256k1>>>();
        
        let mut verifier = Transcript::new(b"sigmatest");
        let proof = SigmaPedersenProof::prove(&mut verifier, &v_vec, &x_vec, &g_vec, &h_vec, &B_vec, n);
        let mut verifier = Transcript::new(b"sigmatest");
        let result = proof.verify(&mut verifier, &B_vec, &g_vec, &h_vec, n);
        assert!(result.is_ok());
    }

    #[test]
    pub fn test_sigma_pedersen_4() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper(&kzen_label, 4);
    }

    #[test]
    pub fn test_sigma_pedersen_8() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper(&kzen_label, 8);
    }

    #[test]
    pub fn test_sigma_pedersen_16() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper(&kzen_label, 16);
    }
    
    #[test]
    pub fn test_sigma_pedersen_32() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper(&kzen_label, 32);
    }

    #[test]
    pub fn test_sigma_pedersen_64() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper(&kzen_label, 64);
    }
}