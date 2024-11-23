#![allow(non_snake_case)]

use curv::{cryptographic_primitives::hashing::DigestExt, elliptic::curves::{Point, Scalar, Secp256k1}};
use sha2::{Digest, Sha256};
use crate::Errors::SigmaPedersenProofError;
use crate::Errors;

pub struct SigmaPedersenProof {
    pub(super) Rj_vec: Vec<Point<Secp256k1>>,
    pub(super) aj_vec: Vec<Scalar<Secp256k1>>,
    pub(super) bj_vec: Vec<Scalar<Secp256k1>>
}

impl SigmaPedersenProof {
    pub fn prove(
        v_vec: &[Scalar<Secp256k1>],
        x_vec: &[Scalar<Secp256k1>],
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        n: usize
    ) -> SigmaPedersenProof {
        assert_eq!(v_vec.len(), n);
        assert_eq!(x_vec.len(), n);
        assert_eq!(g_vec.len(), n);
        assert_eq!(h_vec.len(), n);

        let v_vec = v_vec.to_vec();
        let x_vec = x_vec.to_vec();
        let g_vec = g_vec.to_vec();
        let h_vec = h_vec.to_vec();

        let mut r_vec: Vec<Scalar<Secp256k1>> = Vec::with_capacity(n);
        let mut s_vec: Vec<Scalar<Secp256k1>> = Vec::with_capacity(n);
        for _j in 0..n {
            r_vec.push(Scalar::<Secp256k1>::random());
            s_vec.push(Scalar::<Secp256k1>::random());
        }

        let Rj_vec = (0..n)
            .map(|i| &g_vec[i].clone() * r_vec[i].clone() + &h_vec[i].clone() * s_vec[i].clone())
            .collect::<Vec<Point<Secp256k1>>>();

        let R_vec_input_challenge = (0..Rj_vec.len())
            .map(|i| &Rj_vec[i])
            .collect::<Vec<&Point<Secp256k1>>>();

        let challenge_e: Scalar<Secp256k1> = Sha256::new().chain_points(R_vec_input_challenge).result_scalar();

        let aj_vec = (0..n)
            .map(|i| r_vec[i].clone() + challenge_e.clone() * v_vec[i].clone())
            .collect::<Vec<Scalar<Secp256k1>>>();
        let bj_vec = (0..n)
            .map(|i| s_vec[i].clone() + challenge_e.clone() * x_vec[i].clone())
            .collect::<Vec<Scalar<Secp256k1>>>();

        SigmaPedersenProof {
            Rj_vec,
            aj_vec,
            bj_vec
        }
    }

    pub fn verify(
        &self,
        Bj_vec: &[Point<Secp256k1>],
        g_vec: &[Point<Secp256k1>],
        h_vec: &[Point<Secp256k1>],
        n: usize
    ) -> Result<(), Errors> {
        assert_eq!(Bj_vec.len(), n);
        assert_eq!(g_vec.len(), n);
        assert_eq!(h_vec.len(), n);
        assert_eq!(self.Rj_vec.len(), n);
        assert_eq!(self.aj_vec.len(), n);
        assert_eq!(self.bj_vec.len(), n);

        let Bj_vec = Bj_vec.to_vec();
        let g_vec = g_vec.to_vec();
        let h_vec = h_vec.to_vec();

        let R_vec_input_challenge = (0..n)
            .map(|i| &self.Rj_vec[i])
            .collect::<Vec<&Point<Secp256k1>>>();

        let challenge_e: Scalar<Secp256k1> = Sha256::new().chain_points(R_vec_input_challenge).result_scalar();

        let mut flag = true;

        for j in 0..n {
            if &g_vec[j].clone() * self.aj_vec[j].clone() + &h_vec[j].clone() * self.bj_vec[j].clone() != self.Rj_vec[j].clone() + challenge_e.clone() * Bj_vec[j].clone() {
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
    use sha2::{Digest, Sha512};

    use crate::proofs::varrange::generate_random_point;

    use super::SigmaPedersenProof;

    pub fn test_helper(seed: &BigInt, n: usize) {
        let gi = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to gi:
        let hi = (0..n)
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

        let Bi = (0..n)
            .map(|i| &gi[i].clone() * v_vec[i].clone() + &hi[i].clone() * x_vec[i].clone())
            .collect::<Vec<Point<Secp256k1>>>();

        let proof = SigmaPedersenProof::prove(&v_vec, &x_vec, &gi, &hi, n);
        let result = proof.verify(&Bi, &gi, &hi, n);
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