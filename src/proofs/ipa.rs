#![allow(non_snake_case)]

use curv::{cryptographic_primitives::hashing::DigestExt, elliptic::curves::{secp256_k1::Secp256k1, Point, Scalar}, BigInt};
use curv::arithmetic::traits::*;
use sha2::{Digest, Sha256};

use crate::proofs::vecpoly::inner_product;

use crate::Errors::InnerProductError;
use crate::Errors;

pub struct InnerProductArg {
    pub(super) Al: Vec<Point<Secp256k1>>,
    pub(super) Ar: Vec<Point<Secp256k1>>,
    pub(super) Bl: Vec<Point<Secp256k1>>,
    pub(super) Br: Vec<Point<Secp256k1>>,
    pub(super) a_vec: Vec<BigInt>,
    pub(super) b_vec: Vec<BigInt>
}

impl InnerProductArg {
    pub fn prove(
        G: &[Point<Secp256k1>],
        H: &[Point<Secp256k1>],
        ux: &Point<Secp256k1>,
        a: &[BigInt],
        b: &[BigInt],
        mut Al_vec: Vec<Point<Secp256k1>>,
        mut Ar_vec: Vec<Point<Secp256k1>>,
        mut Bl_vec: Vec<Point<Secp256k1>>,
        mut Br_vec: Vec<Point<Secp256k1>>
    ) -> InnerProductArg {
        let n_hat = G.len();

        // All of the input vectors must have the same length.
        assert_eq!(G.len(), n_hat);
        assert_eq!(H.len(), n_hat);
        assert_eq!(a.len(), n_hat);
        assert_eq!(b.len(), n_hat);
        assert!(n_hat.is_power_of_two());

        if n_hat > 4 {
            let order = Scalar::<Secp256k1>::group_order();

            let n_hat = n_hat / 2;
            let (G_l, G_r) = G.split_at(n_hat);
            let (H_l, H_r) = H.split_at(n_hat);
            let (a_l, a_r) = a.split_at(n_hat);
            let (b_l, b_r) = b.split_at(n_hat);

            let c_l = inner_product(a_r, b_l, order);
            let c_r = inner_product(a_l, b_r, order);

            let c_l_fe = Scalar::<Secp256k1>::from(&c_l);
            let ux_cl = ux * c_l_fe;
            let c_r_fe = Scalar::<Secp256k1>::from(&c_r);
            let ux_cr = ux * c_r_fe;

            let A_l = G_r.iter().zip(a_l).fold(Point::<Secp256k1>::zero(), |acc, x| {
                if x.1 != &BigInt::zero() {
                    let ali = Scalar::<Secp256k1>::from(x.1);
                    let Gri_ali: Point<Secp256k1> = x.0 * &ali;
                    acc + &Gri_ali
                } else {
                    acc
                }
            });

            let A_r = G_l.iter().zip(a_r).fold(Point::<Secp256k1>::zero(), |acc, x| {
                if x.1 != &BigInt::zero() {
                    let ari = Scalar::<Secp256k1>::from(x.1);
                    let Gli_ari: Point<Secp256k1> = x.0 * &ari;
                    acc + &Gli_ari
                } else {
                    acc
                }
            });

            let B_l = H_r.iter().zip(b_l).fold(ux_cl, |acc, x| {
                if x.1 != &BigInt::zero() {
                    let bli = Scalar::<Secp256k1>::from(x.1);
                    let Hri_bli: Point<Secp256k1> = x.0 * &bli;
                    acc + &Hri_bli
                } else {
                    acc
                }
            });

            let B_r = H_l.iter().zip(b_r).fold(ux_cr, |acc, x| {
                if x.1 != &BigInt::zero() {
                    let bri = Scalar::<Secp256k1>::from(x.1);
                    let Hli_bri: Point<Secp256k1> = x.0 * &bri;
                    acc + &Hli_bri
                } else {
                    acc
                }
            });

            let ex: Scalar<Secp256k1> = Sha256::new().chain_points([&A_l, &A_r, &B_l, &B_r, ux]).result_scalar();
            let ex_bn = ex.to_bigint();

            let a_new = (0..n_hat)
                .map(|i| {
                    let ali = a_l[i].clone();
                    let ari_ex = BigInt::mod_mul(&a_r[i], &ex_bn, order);
                    BigInt::mod_add(&ali, &ari_ex, order)
                })
                .collect::<Vec<BigInt>>();
            
            let b_new = (0..n_hat)
                .map(|i| {
                    let bli_ex = BigInt::mod_mul(&b_l[i], &ex_bn, order);
                    let bri = b_r[i].clone();
                    BigInt::mod_add(&bli_ex, &bri, order)
                })
                .collect::<Vec<BigInt>>();

            let G_new = (0..n_hat)
                .map(|i| {
                    let Glex = &G_l[i] * ex.clone();
                    let Gr = &G_r[i];
                    Gr + Glex
                })
                .collect::<Vec<Point<Secp256k1>>>();

            let H_new = (0..n_hat)
                .map(|i| {
                    let Hl = &H_l[i];
                    let Hrex = &H_r[i] * ex.clone();
                    Hl + Hrex
                })
                .collect::<Vec<Point<Secp256k1>>>();

            Al_vec.push(A_l);
            Ar_vec.push(A_r);
            Bl_vec.push(B_l);
            Br_vec.push(B_r);
            return InnerProductArg::prove(&G_new, &H_new, ux, &a_new, &b_new, Al_vec, Ar_vec, Bl_vec, Br_vec);
        }

        InnerProductArg {
            Al: Al_vec,
            Ar: Ar_vec,
            Bl: Bl_vec,
            Br: Br_vec,
            a_vec: a.to_vec(),
            b_vec: b.to_vec()
        }
    }

    pub fn verify(
        &self,
        G: &[Point<Secp256k1>],
        H: &[Point<Secp256k1>],
        ux: &Point<Secp256k1>,
        P: &Point<Secp256k1>,
        Q: &Point<Secp256k1>
    ) -> Result<(), Errors> {
        let n_hat = G.len();

         // All of the input vectors must have the same length.
        assert_eq!(G.len(), n_hat);
        assert_eq!(H.len(), n_hat);
        assert!(n_hat.is_power_of_two());

        let order = Scalar::<Secp256k1>::group_order();

        if n_hat > 4 {
            let n_hat = n_hat / 2;
            let (G_l, G_r) = G.split_at(n_hat);
            let (H_l, H_r) = H.split_at(n_hat);

            let ex: Scalar<Secp256k1> = Sha256::new()
                .chain_points([&self.Al[0], &self.Ar[0], &self.Bl[0], &self.Br[0], ux])
                .result_scalar();
            let ex_bn = ex.to_bigint();
            let ex_sq_bn = BigInt::mod_mul(&ex_bn, &ex_bn, order);
            let ex_sq_fe = Scalar::<Secp256k1>::from(&ex_sq_bn);

            let G_new = (0..n_hat)
                .map(|i| {
                    let Glex = &G_l[i] * ex.clone();
                    let Gr = &G_r[i];
                    Gr + Glex
                })
                .collect::<Vec<Point<Secp256k1>>>();

            let H_new = (0..n_hat)
                .map(|i| {
                    let Hl = &H_l[i];
                    let Hrex = &H_r[i] * ex.clone();
                    Hl + Hrex
                })
                .collect::<Vec<Point<Secp256k1>>>();

            let Pex = P * ex.clone();
            let Arex_sq = &self.Ar[0] * ex_sq_fe.clone();
            let P_tag = self.Al[0].clone() + Pex + Arex_sq;

            let Blex_sq = &self.Bl[0] * ex_sq_fe;
            let Qex = Q * ex;
            let Q_tag = Blex_sq + Qex + self.Br[0].clone();

            let ipa = InnerProductArg {
                Al: self.Al[1..].to_vec(),
                Ar: self.Ar[1..].to_vec(),
                Bl: self.Bl[1..].to_vec(),
                Br: self.Br[1..].to_vec(),
                a_vec: self.a_vec.clone(),
                b_vec: self.b_vec.clone()
            };
            return ipa.verify(&G_new, &H_new, ux, &P_tag, &Q_tag);
        }

        let c = inner_product(&self.a_vec, &self.b_vec, order);
        let ux_c = ux * Scalar::<Secp256k1>::from_bigint(&c);

        let G_a = G.iter().zip(self.a_vec.clone()).fold(Point::<Secp256k1>::zero(), |acc, x| {
            if x.1 != BigInt::zero() {
                let ai = Scalar::<Secp256k1>::from(x.1);
                let Gi_ai: Point<Secp256k1> = x.0 * &ai;
                acc + &Gi_ai
            } else {
                acc
            }
        });

        let H_b_c = H.iter().zip(self.b_vec.clone()).fold(ux_c, |acc, x| {
            if x.1 != BigInt::zero() {
                let bi = Scalar::<Secp256k1>::from(x.1);
                let Hi_bi: Point<Secp256k1> = x.0 * &bi;
                acc + &Hi_bi
            } else {
                acc
            }
        });

        if P.clone() == G_a && Q.clone() == H_b_c {
            Ok(())
        } else {
            Err(InnerProductError)
        }
    }
}

#[cfg(test)]
mod test {
    use curv::{arithmetic::Converter, cryptographic_primitives::hashing::DigestExt, elliptic::curves::{secp256_k1::hash_to_curve::generate_random_point, Point, Scalar, Secp256k1}, BigInt};
    use curv::arithmetic::One;
    use sha2::{Digest, Sha512};

    use crate::proofs::vecpoly::inner_product;
    use super::InnerProductArg;

    fn test_helper(n: usize) {
        let order = Scalar::<Secp256k1>::group_order();
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);

        let g_vec = (0..n)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + &kzen_label;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to g_vec:
        let h_vec = (0..n)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + &kzen_label;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let label = BigInt::one();
        let hash = Sha512::new().chain_bigint(&label).result_bigint();
        let Gx = generate_random_point(&Converter::to_bytes(&hash));

        let a: Vec<_> = (0..n)
            .map(|_| {
                let rand = Scalar::<Secp256k1>::random();
                rand.to_bigint()
            })
            .collect();

        let b: Vec<_> = (0..n)
            .map(|_| {
                let rand = Scalar::<Secp256k1>::random();
                rand.to_bigint()
            })
            .collect();

        let c = inner_product(&a, &b, order);

        let c_fe = Scalar::<Secp256k1>::from(&c);
        let ux_c: Point<Secp256k1> = &Gx * &c_fe;

        let P = (0..n)
            .map(|i| {
                let ai = Scalar::<Secp256k1>::from(&a[i]);
                &g_vec[i] * &ai
            })
            .fold(Point::<Secp256k1>::zero(), |acc, x: Point<Secp256k1>| acc + x as Point<Secp256k1>);

        let Q = (0..n)
            .map(|i| {
                let bi = Scalar::<Secp256k1>::from(&b[i]);
                &h_vec[i] * &bi
            })
            .fold(ux_c, |acc, x: Point<Secp256k1>| acc + x as Point<Secp256k1>);

        let Al_vec: Vec<Point<Secp256k1>> = Vec::with_capacity(n);
        let Ar_vec: Vec<Point<Secp256k1>> = Vec::with_capacity(n);
        let Bl_vec: Vec<Point<Secp256k1>> = Vec::with_capacity(n);
        let Br_vec: Vec<Point<Secp256k1>> = Vec::with_capacity(n);
        let ipa = InnerProductArg::prove(&g_vec, &h_vec, &Gx, &a, &b, Al_vec, Ar_vec, Bl_vec, Br_vec);
        let result = InnerProductArg::verify(&ipa, &g_vec, &h_vec, &Gx, &P, &Q);
        assert!(result.is_ok());
    }

    #[test]
    pub fn test_ipa_2() {
        test_helper(2);
    }
    
    #[test]
    pub fn test_ipa_4() {
        test_helper(4);
    }
    
    #[test]
    pub fn test_ipa_8() {
        test_helper(8);
    }
    
    #[test]
    pub fn test_ipa_16() {
        test_helper(16);
    }

    #[test]
    pub fn test_ipa_32() {
        test_helper(32);
    }

    #[test]
    pub fn test_ipa_64() {
        test_helper(64);
    }

    #[test]
    pub fn test_ipa_128() {
        test_helper(128);
    }

    #[test]
    pub fn test_ipa_256() {
        test_helper(256);
    }

    #[test]
    pub fn test_ipa_512() {
        test_helper(512);
    }

    #[test]
    pub fn test_ipa_1024() {
        test_helper(1024);
    }
}
