#![allow(non_snake_case)]

use generic_array::typenum::Unsigned;
use curv::{cryptographic_primitives::hashing::DigestExt, elliptic::curves::{secp256_k1::Secp256k1, Curve, ECPoint, Point, Scalar}, BigInt};
use curv::arithmetic::traits::*;
use generic_array::GenericArray;
use merlin::Transcript;
use sha2::{Digest, Sha512};
use std::ops::{Shl, Shr};
use itertools::iterate;
use crate::{proofs::transcript::TranscriptProtocol, Errors::{RangeProofError, VarRangeError}};
use crate::Errors;

use super::{ipa::InnerProductArg, sigma_pedersen::SigmaPedersenProof, vec_poly::{inner_product, VecPoly}};

// an argument of knowledge of the vector "L"
// when n*b+b_bar <= 21, this enumeration type is the vector "L" itself
// otherwise it consists of t_hat and an inner product argument(IPA)
#[derive(Clone)]
enum AgKnowledgeVec {
    LVec(Vec<Scalar<Secp256k1>>),
    IPA{ t_hat: BigInt, ip: InnerProductArg}
}

#[derive(Clone)]
pub struct VarRange {
    A: Point<Secp256k1>, // vector commitment to a
    A_hat: Point<Secp256k1>, // vector commitment to a_hat
    B: Point<Secp256k1>, // vector commitment to b
    B_hat: Point<Secp256k1>, // vector commitment to b_hat
    D: Point<Secp256k1>, // vector commitment to d
    T_vec: Vec<Point<Secp256k1>>, // commitment to the 16 non-zero coeffs of M(X)
    AKV: AgKnowledgeVec, // an argument of L, which is the evaluation of poly L(x)
    tau: Scalar<Secp256k1>, // evaluation of poly M(x)
    rho: Scalar<Secp256k1> // used to balance random numbers
}

// before invoking IPA, we should pad the length of vector to power of 2
// pad vectors over the field with 0
fn pad_bn_to_power_of_two(bn_vec: &mut Vec<BigInt>) {
    let current_len = bn_vec.len();
    let target_len = current_len.next_power_of_two();
    for _ in current_len..target_len {
        bn_vec.push(BigInt::zero());
    }
}

// pad vectors over the group with random point
fn pad_point_to_power_of_two(P_vec: &mut Vec<Point<Secp256k1>>, seed: &BigInt) {
    let current_len = P_vec.len();
    let target_len = current_len.next_power_of_two();
    for i in current_len..target_len {
        let kzen_label_i = BigInt::from(i as u32) + seed;
        let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
        let r = generate_random_point(&Converter::to_bytes(&hash_i));
        P_vec.push(r);
    }
}

fn count_bits(mut n: BigInt) -> usize {
    let mut count = 0;
    while n > BigInt::zero() {
        n >>= 1;
        count += 1;
    }
    count
}

pub fn generate_random_point(bytes: &[u8]) -> Point<Secp256k1> {
    let compressed_point_len =
        <<Secp256k1 as Curve>::Point as ECPoint>::CompressedPointLength::USIZE;
    let truncated = if bytes.len() > compressed_point_len - 1 {
        &bytes[0..compressed_point_len - 1]
    } else {
        bytes
    };
    let mut buffer = GenericArray::<
        u8,
        <<Secp256k1 as Curve>::Point as ECPoint>::CompressedPointLength,
    >::default();
    buffer.as_mut_slice()[0] = 0x2;
    buffer.as_mut_slice()[1..1 + truncated.len()].copy_from_slice(truncated);
    if let Ok(point) = Point::from_bytes(buffer.as_slice()) {
        return point;
    }

    let bn = BigInt::from_bytes(bytes);
    let two = BigInt::from(2);
    let bn_times_two = BigInt::mod_mul(&bn, &two, Scalar::<Secp256k1>::group_order());
    let bytes = BigInt::to_bytes(&bn_times_two);
    generate_random_point(&bytes)
}

pub fn print_bool_vec(b_vec: Vec<bool>) {
    for j in 0..b_vec.len() {
        println!("b_vec[{}] is {}", j, b_vec[j]);
    }
}

pub fn print_bn_vec(bn_vec: Vec<BigInt>) {
    for j in 0..bn_vec.len() {
        println!("bn_vec[{}] is {}, ", j, bn_vec[j]);
    }
}

pub fn print_vec_poly(bn_vec: Vec<Vec<BigInt>>, modulus: BigInt) {
    for j in 0..bn_vec.len() {
        for i in 0..bn_vec[0].len() {
            if bn_vec[j][i].clone() * BigInt::from(2) < modulus.clone() {
                print!("{} ", bn_vec[j][i]);
            } else {
                print!("{} ", bn_vec[j][i].clone() - modulus.clone());
            }
        }
    }
}

impl VarRange {
    pub fn range_prove(
        transcript: &mut Transcript,
        gi: &[Point<Secp256k1>],
        hi: &[Point<Secp256k1>],
        values: Vec<Scalar<Secp256k1>>,
        x_vec: Vec<Scalar<Secp256k1>>,
        s: Scalar<Secp256k1>,
        t: Scalar<Secp256k1>,
        n: usize,
        B_vec: &[Point<Secp256k1>],
        seed: &BigInt
    ) -> VarRange {
        let gi = gi.to_vec();
        let hi = hi.to_vec();
        
        assert_eq!(gi.len(), n + 1);
        assert_eq!(hi.len(), n + 1);
        assert_eq!(values.len(), n + 1);
        assert_eq!(x_vec.len(), n + 1);
        assert_eq!(B_vec.len(), n + 1);

        // get b such that 2^{b-1} <= 2s < 2^b and 
        // b_bar such that 2^{b_bar-1} <= t < 2^b_bar
        let b = count_bits(s.to_bigint()) + 1;
        let b_bar = count_bits(t.to_bigint());

        transcript.varrange_domain_sep(n as u64, b as u64, b_bar as u64);
        transcript.append_points_array(b"B_vec", B_vec);

        let rho_a = Scalar::<Secp256k1>::random();
        let rho_a_hat = Scalar::<Secp256k1>::random();
        let rho_b = Scalar::<Secp256k1>::random();
        let rho_b_hat = Scalar::<Secp256k1>::random();
        let rho_d = Scalar::<Secp256k1>::random();

        let kzen_label = seed;
        let hash = Sha512::new().chain_bigint(kzen_label).result_bigint();
        let H = &generate_random_point(&Converter::to_bytes(&hash));
        
        // v_hat_i = s - v_i, i in [n] and v_hat_n+1 = t- v_n+1
        let mut values_hat = (0..n)
            .map(|i| s.clone() - values[i].clone())
            .collect::<Vec<Scalar<Secp256k1>>>();
        values_hat.push(t.clone() - values[n].clone());
        
        // calculate v_i + s, i in [n]
        let temp = values[n].clone();
        let mut values = (0..n)
            .map(|i| s.clone() + values[i].clone())
            .collect::<Vec<Scalar<Secp256k1>>>();
        values.push(temp);
        
        // x_hat = -x
        let x_vec_hat = (0..n+1)
            .map(|i| Scalar::<Secp256k1>::zero() - x_vec[i].clone())
            .collect::<Vec<Scalar<Secp256k1>>>();
        
        // get vector g whose length is n*b+b_bar
        let mut g_vec: Vec<Point<Secp256k1>> = Vec::new();
        for j in 0..n {
            g_vec.push(gi[j].clone());
            g_vec.push(hi[j].clone());

            let mut ui = (0..b-2)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed + BigInt::from((j * (b-2) + 1) as u32);
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

            g_vec.append(&mut ui);
        }
        g_vec.push(gi[n].clone());
        g_vec.push(hi[n].clone());
        let mut ui = (0..b_bar-2)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed + BigInt::from((n * (b-2) + 1) as u32);
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();
        g_vec.append(&mut ui);

        transcript.append_points_array(b"g_vec", &g_vec);

        let mut A = H * &rho_a;
        let mut A_hat = H * &rho_a_hat;
        let mut B = H * &rho_b;
        let mut B_hat = H * &rho_b_hat;
        let mut D = H * &rho_d;

        let order = Scalar::<Secp256k1>::group_order();
        let two = BigInt::from(2);
        let one = BigInt::one();
        
        // get the first n val in the values and values_hat
        // which bit_length is b
        let mut values_n= values[0..n].to_vec();
        let mut values_hat_n = values_hat[0..n].to_vec();

        // concat all values and values_hat
        values_n.reverse();
        let values_agg = values_n
            .iter()
            .fold(values[n].to_bigint(), |acc, x| acc.shl(b) + x.to_bigint());
        values_hat_n.reverse();
        let values_hat_agg = values_hat_n
            .iter()
            .fold(values_hat[n].to_bigint(), |acc, x| acc.shl(b) + x.to_bigint());
        
        let a_vec = (0..n*b+b_bar)
            .map(|i| {
                let shr_secret = values_agg.clone().shr(i);
                shr_secret.modulus(&two)
            })
            .collect::<Vec<BigInt>>();
        let b_vec = (0..n*b+b_bar)
            .map(|i| BigInt::mod_sub(&a_vec[i], &one, order))
            .collect::<Vec<BigInt>>();

        let a_vec_hat = (0..n*b+b_bar)
            .map(|i| {
                let shr_secret = values_hat_agg.clone().shr(i);
                shr_secret.modulus(&two)
            })
            .collect::<Vec<BigInt>>();
        let b_vec_hat = (0..n*b+b_bar)
            .map(|i| BigInt::mod_sub(&a_vec_hat[i], &one, order))
            .collect::<Vec<BigInt>>();

        let values_bits = (0..n*b+b_bar)
            .map(|i| {
                let bignum_bit: BigInt = a_vec[i].clone() & BigInt::one();
                let byte = BigInt::to_bytes(&bignum_bit);
                byte[0] == 1
            })
            .collect::<Vec<bool>>();

        let values_hat_bits = (0..n*b+b_bar)
            .map(|i| {
                let bignum_bit: BigInt = a_vec_hat[i].clone() & BigInt::one();
                let byte = BigInt::to_bytes(&bignum_bit);
                byte[0] == 1
            })
            .collect::<Vec<bool>>();
        
        // construct c_vec and c_vec_hat
        let zero_vec = vec![BigInt::zero(); b - 2];
        let zero_vec_bar = vec![BigInt::zero(); b_bar - 2];

        values_n.reverse();
        let mut c_vec: Vec<BigInt> = values_n.iter()
            .zip(x_vec.iter())
            .flat_map(|(vi, xi)| {
                let mut result = vec![vi.to_bigint(), xi.to_bigint()];
                result.extend_from_slice(&zero_vec);
                result
            })
            .collect();
        c_vec.append(&mut vec![values[n].to_bigint(), x_vec[n].to_bigint()]);
        c_vec.append(&mut zero_vec_bar.clone());

        values_hat_n.reverse();
        let mut c_vec_hat: Vec<BigInt> = values_hat_n.iter()
            .zip(x_vec_hat.iter())
            .flat_map(|(vi, xi)| {
                let mut result = vec![vi.to_bigint(), xi.to_bigint()];
                result.extend_from_slice(&zero_vec);
                result
            })
            .collect();
        c_vec_hat.append(&mut vec![values_hat[n].to_bigint(), x_vec_hat[n].to_bigint()]);
        c_vec_hat.append(&mut zero_vec_bar.clone());
        let mut index: usize = 0;

        A = g_vec.iter().zip(values_bits.clone()).fold(
            A,
            |acc, x| {
                if x.1 {
                    acc + x.0
                } else {
                    acc
                }
            },
        );

        A_hat = g_vec.iter().zip(values_hat_bits.clone()).fold(
            A_hat,
            |acc, x| {
                if x.1 {
                    acc + x.0
                } else {
                    acc
                }
            },
        );

        B = g_vec
            .iter()
            .zip(values_bits)
            .fold(B, |acc, x| if !x.1 { acc - x.0 } else { acc });

        B_hat = g_vec
            .iter()
            .zip(values_hat_bits)
            .fold(B_hat, |acc, x| if !x.1 { acc - x.0 } else { acc });

        let d_vec = (0..n*b+b_bar)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        D = d_vec.iter().fold(D, |acc, x| {
                let g_vec_i_di = &g_vec[index] * x;
                index += 1;
                acc + g_vec_i_di
            });

        transcript.append_point(b"A", &A);
        transcript.append_point(b"A_hat", &A_hat);
        transcript.append_point(b"B", &B);
        transcript.append_point(b"B_hat", &B_hat);
        transcript.append_point(b"D", &D);
        
        let y = transcript.challenge_scalar(b"y");
        let y_bn = y.to_bigint();
        let one_fe = Scalar::<Secp256k1>::from(&one);
        let yi = iterate(one_fe.clone(), |i| i.clone() * &y)
            .take(n*b+b_bar)
            .collect::<Vec<Scalar<Secp256k1>>>();

        let d_vec_bn = (0..n*b+b_bar)
                .map(|i| d_vec[i].to_bigint())
                .collect::<Vec<BigInt>>();

        let y_nb_plus_b_bar = (yi[n*b+b_bar - 1].clone() * y.clone()).to_bigint();
        let zero_vec_nb_plus_b_bar = vec![BigInt::zero(); n*b+b_bar];
        let y_nb_plus_b_bar_a_vec_hat = (0..n*b+b_bar)
            .map(|i| BigInt::mod_mul(&y_nb_plus_b_bar, &a_vec_hat[i], order))
            .collect::<Vec<BigInt>>();
        
        // construct the poly L(X)
        let L_coeff_vec: Vec<Vec<BigInt>> = vec![
            zero_vec_nb_plus_b_bar.clone(),
            zero_vec_nb_plus_b_bar.clone(),
            b_vec_hat.clone(),
            b_vec,
            zero_vec_nb_plus_b_bar.clone(),
            a_vec,
            y_nb_plus_b_bar_a_vec_hat,
            c_vec,
            c_vec_hat,
            d_vec_bn,
        ];

        // the lowest power is -4, so the offset is 4
        let L_poly = VecPoly::new(L_coeff_vec.clone(), order.clone(), 4);

        let two_vec_b = (0..b)
            .map(|i| BigInt::mod_pow(&two, &BigInt::from(i as u64), order))
            .collect::<Vec<BigInt>>();
        let two_vec_b_bar = (0..b_bar)
            .map(|i| BigInt::mod_pow(&two, &BigInt::from(i as u64), order))
            .collect::<Vec<BigInt>>();
        let mut zero_vec_b = vec![BigInt::zero(); b];
        zero_vec_b[0] = one.clone();
        let mut zero_vec_b_bar = vec![BigInt::zero(); b_bar];
        zero_vec_b_bar[0] = one.clone();

        let y_2_nb_plus_b_bar = BigInt::mod_pow(&y_nb_plus_b_bar, &two, order);
        let y_3_nb_plus_b_bar = BigInt::mod_pow(&y_nb_plus_b_bar, &BigInt::from(3), order);
        let y_4_nb_plus_b_bar = BigInt::mod_pow(&y_nb_plus_b_bar, &BigInt::from(4), order);
        let y_3_nb_plus_b_bar_plus_n = BigInt::mod_mul(&y_3_nb_plus_b_bar, &yi[n].to_bigint(), order);
        let y_4_nb_plus_b_bar_plus_n = BigInt::mod_mul(&y_4_nb_plus_b_bar, &yi[n].to_bigint(), order);
        let mut temp_vec: Vec<BigInt>;
        
        // construct the poly R
        let r_neg_1_1 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_mul(&y_2_nb_plus_b_bar, &yi[i].to_bigint(), order))
            .collect::<Vec<BigInt>>();
        
        temp_vec = (0..b)
            .map(|i| BigInt::mod_mul(&y_4_nb_plus_b_bar, &two_vec_b[i], order))
            .collect::<Vec<BigInt>>();
        let mut r_neg_1_2: Vec<BigInt> = Vec::new();
        for _j in 0..n {
            r_neg_1_2.append(&mut temp_vec.clone());

            temp_vec = (0..b)
                .map(|i| BigInt::mod_mul(&y_bn, &temp_vec[i], order))
                .collect::<Vec<BigInt>>();
        }
        temp_vec = (0..b_bar)
            .map(|i| BigInt::mod_mul(&y_4_nb_plus_b_bar_plus_n, &two_vec_b_bar[i], order))
            .collect::<Vec<BigInt>>();
        r_neg_1_2.append(&mut temp_vec);

        let r_neg_1 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_add(&r_neg_1_1[i], &r_neg_1_2[i], order))
            .collect::<Vec<BigInt>>();

        let r_neg_2_1 = r_neg_1_1.clone();

        temp_vec = (0..b)
            .map(|i| BigInt::mod_mul(&y_3_nb_plus_b_bar_plus_n, &two_vec_b[i], order))
            .collect::<Vec<BigInt>>();
        let mut r_neg_2_2: Vec<BigInt> = Vec::new();
        for _j in 0..n {
            temp_vec = (0..b)
                .map(|i| BigInt::mod_mul(&y_bn, &temp_vec[i], order))
                .collect::<Vec<BigInt>>();

            r_neg_2_2.append(&mut temp_vec.clone());
        }
        let y_3_nb_plus_b_bar_plus_2n_plus_1 = BigInt::mod_pow(&y_bn, &BigInt::from((3*(n*b+b_bar)+2*n+1) as u64), order);
        temp_vec = (0..b_bar)
            .map(|i| BigInt::mod_mul(&y_3_nb_plus_b_bar_plus_2n_plus_1, &two_vec_b_bar[i], order))
            .collect::<Vec<BigInt>>();
        r_neg_2_2.append(&mut temp_vec);

        let r_neg_2 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_add(&r_neg_2_1[i], &r_neg_2_2[i], order))
            .collect::<Vec<BigInt>>();

        let r_1 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_mul(&(order-one.clone()), &r_neg_1_1[i], order))
            .collect::<Vec<BigInt>>();

        let r_2 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_mul(&(order-y_3_nb_plus_b_bar.clone()), &yi[i].to_bigint(), order))
            .collect::<Vec<BigInt>>();

        temp_vec = (0..b)
            .map(|i| BigInt::mod_mul(&(order-y_4_nb_plus_b_bar.clone()), &zero_vec_b[i], order))
            .collect::<Vec<BigInt>>();
        let mut r_neg_3: Vec<BigInt> = Vec::new();
        for _j in 0..n {
            r_neg_3.append(&mut temp_vec.clone());

            temp_vec = (0..b)
                .map(|i| BigInt::mod_mul(&y_bn, &temp_vec[i], order))
                .collect::<Vec<BigInt>>();
        }
        temp_vec = (0..b_bar)
            .map(|i| BigInt::mod_mul(&(order-y_4_nb_plus_b_bar_plus_n.clone()), &zero_vec_b_bar[i], order))
            .collect::<Vec<BigInt>>();
        r_neg_3.append(&mut temp_vec);

        temp_vec = (0..b)
            .map(|i| BigInt::mod_mul(&(order-y_4_nb_plus_b_bar_plus_n.clone()), &zero_vec_b[i], order))
            .collect::<Vec<BigInt>>();
        let mut r_neg_4: Vec<BigInt> = Vec::new();
        for _j in 0..n {
            temp_vec = (0..b)
                .map(|i| BigInt::mod_mul(&y_bn, &temp_vec[i], order))
                .collect::<Vec<BigInt>>();

            r_neg_4.append(&mut temp_vec.clone());
        }
        let y_4_nb_plus_b_bar_plus_2n_plus_1 = BigInt::mod_pow(&y_bn, &BigInt::from((4*(n*b+b_bar)+2*n+1) as u64), order);
        temp_vec = (0..b_bar)
            .map(|i| BigInt::mod_mul(&(order-y_4_nb_plus_b_bar_plus_2n_plus_1.clone()), &zero_vec_b_bar[i], order))
            .collect::<Vec<BigInt>>();
        r_neg_4.append(&mut temp_vec);
        
        let R_coeff_vec: Vec<Vec<BigInt>> = vec![
            r_neg_4,
            r_neg_3,
            r_neg_2,
            r_neg_1,
            zero_vec_nb_plus_b_bar.clone(),
            r_1,
            r_2,
            zero_vec_nb_plus_b_bar.clone(),
            zero_vec_nb_plus_b_bar.clone(),
            zero_vec_nb_plus_b_bar.clone(),
        ];

        let mut L_otimes_yi: Vec<Vec<BigInt>> = Vec::new();
        for j in 0..L_coeff_vec.len() {
            temp_vec = (0..n*b+b_bar)
                .map(|i| BigInt::mod_mul(&L_coeff_vec[j][i], &yi[i].to_bigint(), order))
                .collect::<Vec<BigInt>>();

            L_otimes_yi.push(temp_vec);
        }

        let mut temp_poly_coeff_vec: Vec<Vec<BigInt>> = Vec::new();
        for j in 0..L_otimes_yi.len() {
            temp_vec = (0..n*b+b_bar)
                .map(|i| BigInt::mod_add(&L_otimes_yi[j][i], &(two.clone() * R_coeff_vec[j][i].clone()), order))
                .collect::<Vec<BigInt>>();

            temp_poly_coeff_vec.push(temp_vec);
        }

        let temp_poly = VecPoly::new(temp_poly_coeff_vec, order.clone(), 4);
        let mut M_poly = L_poly.clone() * temp_poly;

        temp_vec = (0..n*b+b_bar)
            .map(|i| BigInt::mod_mul(&(y_2_nb_plus_b_bar.clone() + y_3_nb_plus_b_bar.clone()), &yi[i].to_bigint(), order))
            .collect::<Vec<BigInt>>();
        let one_vec = vec![one.clone(); n*b+b_bar];

        // the 8th element is const (i.e. the offset of M_poly is 8, but M[0]=M[1]=0) 
        // the we need prove M[8] = 0
        M_poly[8] = BigInt::mod_sub(&M_poly[8], &(two.clone() * inner_product(&one_vec, &temp_vec, order)), order);
        
        // M_poly[0] = M_plot[1] = 0, we need to commit the non-zero coeff
        // i.e. M[2], ..., M[18], without M[8]
        let tau_vec = (2..M_poly.len())
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();
        let mut T_vec = (2..M_poly.len())
            .map(|i| H * tau_vec[i-2].clone() + &g_vec[0] * Scalar::<Secp256k1>::from_bigint(&M_poly[i]))
            .collect::<Vec<Point<Secp256k1>>>();
        T_vec.remove(6);

        transcript.append_points_array(b"T_vec", &T_vec);
        let challenge_x: Scalar<Secp256k1> = transcript.challenge_scalar(b"x");

        let L_bn = L_poly.clone().evaluate(&challenge_x.to_bigint());
        let L = (0..L_bn.len())
            .map(|i| Scalar::<Secp256k1>::from_bigint(&L_bn[i]))
            .collect::<Vec<Scalar<Secp256k1>>>();
        
        // M_poly[0] = M_plot[1] = 0, we need to commit the non-zero coeff
        // i.e. M[2], ..., M[18], without M[8]
        let mut tau_bn = BigInt::zero();
        let mut x_power;
        for i in 2..M_poly.len() {
            if i < 8 {
                x_power = BigInt::mod_pow(&challenge_x.to_bigint(), &(order + BigInt::from(i as i32 - 9)), order);
            } else if i == 8 {
                continue;
            } else {
                x_power = BigInt::mod_pow(&challenge_x.to_bigint(), &(BigInt::from((i - 8) as i32)), order);
            }
            tau_bn = BigInt::mod_add(&tau_bn, &(tau_vec[i-2].to_bigint().clone() * x_power), order);
        }
        let tau = Scalar::<Secp256k1>::from_bigint(&tau_bn);
        
        // use Fermat's Little Theorem to find the inverse
        let x_neg_1 = BigInt::mod_pow(&challenge_x.to_bigint(), &(order - one.clone() - one.clone()), order);
        let x_neg_2 = BigInt::mod_pow(&challenge_x.to_bigint(), &(order - one.clone() - two.clone()), order);
        let x_2 = BigInt::mod_pow(&challenge_x.to_bigint(), &two, order);
        let x_5 = BigInt::mod_pow(&challenge_x.to_bigint(), &BigInt::from(5), order);
        let mut rho_bn = BigInt::mod_mul(&rho_a.to_bigint(), &challenge_x.to_bigint(), order);
        rho_bn = BigInt::mod_add(&rho_bn, &BigInt::mod_mul(&rho_b.to_bigint(), &x_neg_1, order), order);
        rho_bn = BigInt::mod_add(&rho_bn, &BigInt::mod_mul(&(rho_a_hat.to_bigint()*y_nb_plus_b_bar.clone()), &x_2, order), order);
        rho_bn = BigInt::mod_add(&rho_bn, &BigInt::mod_mul(&rho_b_hat.to_bigint(), &x_neg_2, order), order);
        rho_bn = BigInt::mod_add(&rho_bn, &BigInt::mod_mul(&rho_d.to_bigint(), &x_5, order), order);
        let rho = Scalar::<Secp256k1>::from_bigint(&rho_bn);

        transcript.append_scalar(b"tau", &tau);
        transcript.append_scalar(b"rho", &rho);
        
        let AKV: AgKnowledgeVec;
        if n*b+b_bar <= 21 {
            // if n*b+b_bar <= 21, V is L
            AKV = AgKnowledgeVec::LVec(L);
        } else {
            // otherwise we need to invoke IPA
            let R_poly = VecPoly::new(R_coeff_vec, order.clone(), 4);
            let R = R_poly.evaluate(&challenge_x.to_bigint());
            
            // evaluate M(x)
            let mut t_hat = BigInt::zero();
            for i in 2..M_poly.len() {
                if i < 8 {
                    x_power = BigInt::mod_pow(&challenge_x.to_bigint(), &(order + BigInt::from(i as i32 - 9)), order);
                } else if i == 8 {
                    continue;
                } else {
                    x_power = BigInt::mod_pow(&challenge_x.to_bigint(), &(BigInt::from((i - 8) as i32)), order);
                }
                t_hat = BigInt::mod_add(&t_hat, &(M_poly[i].clone() * x_power), order);
            }

            let y_inv = y.clone().invert().unwrap();
            let yi_inv = iterate(one_fe.clone(), |i| i.clone() * &y_inv)
                .take(n*b+b_bar)
                .collect::<Vec<Scalar<Secp256k1>>>();

            let mut h_vec = (0..n*b+b_bar)
                .map(|i| &g_vec[i] * yi_inv[i].clone())
                .collect::<Vec<Point<Secp256k1>>>();

            let mut a_ipa_vec = (0..n*b+b_bar)
                .map(|i| L[i].clone().to_bigint())
                .collect::<Vec<BigInt>>();

            temp_vec = (0..n*b+b_bar)
                .map(|i| BigInt::mod_mul(&yi[i].to_bigint(), &L[i].to_bigint(), order))
                .collect::<Vec<BigInt>>();
            let mut b_ipa_vec = (0..n*b+b_bar)
                .map(|i| BigInt::mod_add(&temp_vec[i], &(R[i].clone() * two.clone()), order))
                .collect::<Vec<BigInt>>();

            let kzen_label = seed + BigInt::from((n*b+b_bar) as u32);
            let hash = Sha512::new().chain_bigint(&kzen_label).result_bigint();
            let q = generate_random_point(&Converter::to_bytes(&hash));
            
            // ux = q^c
            transcript.append_points_array(b"g_vec", &g_vec);
            transcript.append_points_array(b"h_vec", &h_vec);
            let cx: Scalar<Secp256k1> = transcript.challenge_scalar(b"c");
            let ux = &q * cx;

            // pad
            pad_point_to_power_of_two(&mut g_vec, &(seed + BigInt::from((n*b+b_bar+1) as u32)));
            pad_point_to_power_of_two(&mut h_vec, &(seed + BigInt::from((n*b+b_bar+1+g_vec.len()) as u32)));
            pad_bn_to_power_of_two(&mut a_ipa_vec);
            pad_bn_to_power_of_two(&mut b_ipa_vec);

            let Al_vec: Vec<Point<Secp256k1>> = Vec::with_capacity(n);
            let Ar_vec: Vec<Point<Secp256k1>> = Vec::with_capacity(n);
            let Bl_vec: Vec<Point<Secp256k1>> = Vec::with_capacity(n);
            let Br_vec: Vec<Point<Secp256k1>> = Vec::with_capacity(n);
            let ip = InnerProductArg::prove(transcript, &g_vec, &h_vec, &ux, &a_ipa_vec, &b_ipa_vec, Al_vec, Ar_vec, Bl_vec, Br_vec);
            AKV = AgKnowledgeVec::IPA { t_hat: (t_hat), ip: (ip) };
        }

        VarRange {
            A,
            A_hat,
            B,
            B_hat,
            D,
            T_vec,
            AKV,
            tau,
            rho
        }
    }

    pub fn range_verify(
        &self,
        transcript: &mut Transcript,
        gi: &[Point<Secp256k1>],
        hi: &[Point<Secp256k1>],
        B_vec: &[Point<Secp256k1>],
        s: Scalar<Secp256k1>,
        t: Scalar<Secp256k1>,
        n: usize,
        seed: &BigInt
    ) -> Result<(), Errors> {
        let b = count_bits(s.to_bigint()) + 1;
        let b_bar = count_bits(t.to_bigint());

        assert_eq!(gi.len(), n + 1);
        assert_eq!(hi.len(), n + 1);
        assert_eq!(B_vec.len(), n + 1);
        
        transcript.varrange_domain_sep(n as u64, b as u64, b_bar as u64);
        transcript.append_points_array(b"B_vec", B_vec);

        let kzen_label = seed;
        let hash = Sha512::new().chain_bigint(kzen_label).result_bigint();
        let H = &generate_random_point(&Converter::to_bytes(&hash));

        let gi = gi.to_vec();
        let hi = hi.to_vec();
        let B_vec = B_vec.to_vec();

        let mut C_vec_hat = (0..n)
            .map(|i| &gi[i] * s.clone() - B_vec[i].clone())
            .collect::<Vec<Point<Secp256k1>>>();
        C_vec_hat.push(&gi[n] * t.clone() - B_vec[n].clone());
        
        let temp = B_vec[n].clone();
        let mut C_vec = (0..n)
            .map(|i| &gi[i] * s.clone() + B_vec[i].clone())
            .collect::<Vec<Point<Secp256k1>>>();
        C_vec.push(temp);

        let order = Scalar::<Secp256k1>::group_order();
        let two = BigInt::from(2);
        let one = BigInt::one();

        let mut g_vec: Vec<Point<Secp256k1>> = Vec::new();
        for j in 0..n {
            g_vec.push(gi[j].clone());
            g_vec.push(hi[j].clone());

            let mut ui = (0..b-2)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed + BigInt::from((j * (b-2) + 1) as u32);
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

            g_vec.append(&mut ui);
        }
        g_vec.push(gi[n].clone());
        g_vec.push(hi[n].clone());
        let mut ui = (0..b_bar-2)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed + BigInt::from((n * (b-2) + 1) as u32);
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        g_vec.append(&mut ui);

        transcript.append_points_array(b"g_vec", &g_vec);
        

        assert_eq!(self.T_vec.len(), 16);

        transcript.append_point(b"A", &self.A);
        transcript.append_point(b"A_hat", &self.A_hat);
        transcript.append_point(b"B", &self.B);
        transcript.append_point(b"B_hat", &self.B_hat);
        transcript.append_point(b"D", &self.D);

        let y = transcript.challenge_scalar(b"y");
        let y_bn = y.to_bigint();
        let one_fe = Scalar::<Secp256k1>::from(&one);
        let yi = iterate(one_fe.clone(), |i| i.clone() * &y)
            .take(n*b+b_bar)
            .collect::<Vec<Scalar<Secp256k1>>>();

        let y_nb_plus_b_bar = (yi[n*b+b_bar - 1].clone() * y.clone()).to_bigint();
        let zero_vec_nb_plus_b_bar = vec![BigInt::zero(); n*b+b_bar];

        let two_vec_b = (0..b)
            .map(|i| BigInt::mod_pow(&two, &BigInt::from(i as u64), order))
            .collect::<Vec<BigInt>>();
        let two_vec_b_bar = (0..b_bar)
            .map(|i| BigInt::mod_pow(&two, &BigInt::from(i as u64), order))
            .collect::<Vec<BigInt>>();
        let mut zero_vec_b = vec![BigInt::zero(); b];
        zero_vec_b[0] = one.clone();
        let mut zero_vec_b_bar = vec![BigInt::zero(); b_bar];
        zero_vec_b_bar[0] = one.clone();

        let y_2_nb_plus_b_bar = BigInt::mod_pow(&y_nb_plus_b_bar, &two, order);
        let y_3_nb_plus_b_bar = BigInt::mod_pow(&y_nb_plus_b_bar, &BigInt::from(3), order);
        let y_4_nb_plus_b_bar = BigInt::mod_pow(&y_nb_plus_b_bar, &BigInt::from(4), order);
        let y_3_nb_plus_b_bar_plus_n = BigInt::mod_mul(&y_3_nb_plus_b_bar, &yi[n].to_bigint(), order);
        let y_4_nb_plus_b_bar_plus_n = BigInt::mod_mul(&y_4_nb_plus_b_bar, &yi[n].to_bigint(), order);
        let mut temp_vec: Vec<BigInt>;
        
        let r_neg_1_1 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_mul(&y_2_nb_plus_b_bar, &yi[i].to_bigint(), order))
            .collect::<Vec<BigInt>>();
        
        temp_vec = (0..b)
            .map(|i| BigInt::mod_mul(&y_4_nb_plus_b_bar, &two_vec_b[i], order))
            .collect::<Vec<BigInt>>();
        let mut r_neg_1_2: Vec<BigInt> = Vec::new();
        for _j in 0..n {
            r_neg_1_2.append(&mut temp_vec.clone());

            temp_vec = (0..b)
                .map(|i| BigInt::mod_mul(&y_bn, &temp_vec[i], order))
                .collect::<Vec<BigInt>>();
        }
        temp_vec = (0..b_bar)
            .map(|i| BigInt::mod_mul(&y_4_nb_plus_b_bar_plus_n, &two_vec_b_bar[i], order))
            .collect::<Vec<BigInt>>();
        r_neg_1_2.append(&mut temp_vec);

        let r_neg_1 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_add(&r_neg_1_1[i], &r_neg_1_2[i], order))
            .collect::<Vec<BigInt>>();

        let r_neg_2_1 = r_neg_1_1.clone();

        temp_vec = (0..b)
            .map(|i| BigInt::mod_mul(&y_3_nb_plus_b_bar_plus_n, &two_vec_b[i], order))
            .collect::<Vec<BigInt>>();
        let mut r_neg_2_2: Vec<BigInt> = Vec::new();
        for _j in 0..n {
            temp_vec = (0..b)
                .map(|i| BigInt::mod_mul(&y_bn, &temp_vec[i], order))
                .collect::<Vec<BigInt>>();

            r_neg_2_2.append(&mut temp_vec.clone());
        }
        let y_3_nb_plus_b_bar_plus_2n_plus_1 = BigInt::mod_pow(&y_bn, &BigInt::from((3*(n*b+b_bar)+2*n+1) as u64), order);
        temp_vec = (0..b_bar)
            .map(|i| BigInt::mod_mul(&y_3_nb_plus_b_bar_plus_2n_plus_1, &two_vec_b_bar[i], order))
            .collect::<Vec<BigInt>>();
        r_neg_2_2.append(&mut temp_vec);

        let r_neg_2 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_add(&r_neg_2_1[i], &r_neg_2_2[i], order))
            .collect::<Vec<BigInt>>();

        let r_1 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_mul(&(order-one.clone()), &r_neg_1_1[i], order))
            .collect::<Vec<BigInt>>();

        let r_2 = (0..n*b+b_bar)
            .map(|i| BigInt::mod_mul(&(order-y_3_nb_plus_b_bar.clone()), &yi[i].to_bigint(), order))
            .collect::<Vec<BigInt>>();

        temp_vec = (0..b)
            .map(|i| BigInt::mod_mul(&(order-y_4_nb_plus_b_bar.clone()), &zero_vec_b[i], order))
            .collect::<Vec<BigInt>>();
        let mut r_neg_3: Vec<BigInt> = Vec::new();
        for _j in 0..n {
            r_neg_3.append(&mut temp_vec.clone());

            temp_vec = (0..b)
                .map(|i| BigInt::mod_mul(&y_bn, &temp_vec[i], order))
                .collect::<Vec<BigInt>>();
        }
        temp_vec = (0..b_bar)
            .map(|i| BigInt::mod_mul(&(order-y_4_nb_plus_b_bar_plus_n.clone()), &zero_vec_b_bar[i], order))
            .collect::<Vec<BigInt>>();
        r_neg_3.append(&mut temp_vec);

        temp_vec = (0..b)
            .map(|i| BigInt::mod_mul(&(order-y_4_nb_plus_b_bar_plus_n.clone()), &zero_vec_b[i], order))
            .collect::<Vec<BigInt>>();
        let mut r_neg_4: Vec<BigInt> = Vec::new();
        for _j in 0..n {
            temp_vec = (0..b)
                .map(|i| BigInt::mod_mul(&y_bn, &temp_vec[i], order))
                .collect::<Vec<BigInt>>();

            r_neg_4.append(&mut temp_vec.clone());
        }
        let y_4_nb_plus_b_bar_plus_2n_plus_1 = BigInt::mod_pow(&y_bn, &BigInt::from((4*(n*b+b_bar)+2*n+1) as u64), order);
        temp_vec = (0..b_bar)
            .map(|i| BigInt::mod_mul(&(order-y_4_nb_plus_b_bar_plus_2n_plus_1.clone()), &zero_vec_b_bar[i], order))
            .collect::<Vec<BigInt>>();
        r_neg_4.append(&mut temp_vec);
        
        let R_coeff_vec: Vec<Vec<BigInt>> = vec![
            r_neg_4,
            r_neg_3,
            r_neg_2,
            r_neg_1,
            zero_vec_nb_plus_b_bar.clone(),
            r_1,
            r_2,
            zero_vec_nb_plus_b_bar.clone(),
            zero_vec_nb_plus_b_bar.clone(),
            zero_vec_nb_plus_b_bar,
        ];
        let R_poly = VecPoly::new(R_coeff_vec, order.clone(), 4);

        transcript.append_points_array(b"T_vec", &self.T_vec);
        let challenge_x: Scalar<Secp256k1> = transcript.challenge_scalar(b"x");

        let R = R_poly.evaluate(&challenge_x.to_bigint());
        
        transcript.append_scalar(b"tau", &self.tau);
        transcript.append_scalar(b"rho", &self.rho);
        
        match &self.AKV {
            AgKnowledgeVec::LVec(L) => {
                let L = L.clone();
                assert_eq!(L.len(), n*b+b_bar);

                temp_vec = (0..n*b+b_bar)
                    .map(|i| BigInt::mod_mul(&yi[i].to_bigint(), &L[i].to_bigint(), order))
                    .collect::<Vec<BigInt>>();
                temp_vec = (0..n*b+b_bar)
                    .map(|i| BigInt::mod_add(&temp_vec[i], &(R[i].clone() * two.clone()), order))
                    .collect::<Vec<BigInt>>();
                let L_bn = (0..n*b+b_bar)
                    .map(|i| L[i].to_bigint())
                    .collect::<Vec<BigInt>>();
                let mut t_hat = inner_product(&L_bn, &temp_vec, order);

                temp_vec = (0..n*b+b_bar)
                    .map(|i| BigInt::mod_mul(&(y_2_nb_plus_b_bar.clone() + y_3_nb_plus_b_bar.clone()), &yi[i].to_bigint(), order))
                    .collect::<Vec<BigInt>>();
                let one_vec = vec![one.clone(); n*b+b_bar];

                t_hat = BigInt::mod_sub(&t_hat, &(two.clone() * inner_product(&one_vec, &temp_vec, order)), order);
                let t_hat = Scalar::<Secp256k1>::from_bigint(&t_hat);
                
                let x_neg_1 = BigInt::mod_pow(&challenge_x.to_bigint(), &(order - one.clone() - one.clone()), order);
                let x_neg_2 = BigInt::mod_pow(&challenge_x.to_bigint(), &(order - one.clone() - two.clone()), order);
                let x_2 = BigInt::mod_pow(&challenge_x.to_bigint(), &two, order);
                let x_3 = BigInt::mod_pow(&challenge_x.to_bigint(), &BigInt::from(3), order);
                let x_4 = BigInt::mod_pow(&challenge_x.to_bigint(), &BigInt::from(4), order);
                let x_5 = BigInt::mod_pow(&challenge_x.to_bigint(), &BigInt::from(5), order);
        
                let x_neg_2 = Scalar::<Secp256k1>::from_bigint(&x_neg_2);
                let x_neg_1 = Scalar::<Secp256k1>::from_bigint(&x_neg_1);
                let x_2 = Scalar::<Secp256k1>::from_bigint(&x_2);
                let x_3 = Scalar::<Secp256k1>::from_bigint(&x_3);
                let x_4 = Scalar::<Secp256k1>::from_bigint(&x_4);
                let x_5 = Scalar::<Secp256k1>::from_bigint(&x_5);
                let y_nb_plus_b_bar = Scalar::<Secp256k1>::from_bigint(&y_nb_plus_b_bar);

                let mut g_vec_L = &self.A * challenge_x.clone();
                g_vec_L = &g_vec_L + &self.B * x_neg_1;
                g_vec_L = &g_vec_L + &self.A_hat * y_nb_plus_b_bar * x_2;
                g_vec_L = &g_vec_L + &self.B_hat * x_neg_2;
                for j in 0..n+1 {
                    g_vec_L = &g_vec_L + &C_vec[j] * &x_3;
                    g_vec_L = &g_vec_L + &C_vec_hat[j] * &x_4;
                }
                g_vec_L = &g_vec_L + &self.D * x_5;
                g_vec_L = &g_vec_L - H * self.rho.clone();

                let mut index = 0;
                let g_vec_L_expect = L.iter().fold(Point::<Secp256k1>::zero(), |acc, x| {
                    let g_vec_i_di = &g_vec[index] * x.clone();
                    index += 1;
                    acc + g_vec_i_di
                });

                let g_1_t_hat_h_tau_expect = &g_vec[0] * t_hat + H * self.tau.clone();

                let mut g_1_t_hat_h_tau = Point::<Secp256k1>::zero();
                for j in 0..6 {
                    let x_power = BigInt::mod_pow(&challenge_x.to_bigint(), &(order - one.clone() + BigInt::from(j-6_i32)), order);
                    g_1_t_hat_h_tau = &g_1_t_hat_h_tau + &self.T_vec[j as usize] * Scalar::<Secp256k1>::from_bigint(&x_power);
                }
                for j in 6..16 {
                    let x_power = BigInt::mod_pow(&challenge_x.to_bigint(), &(BigInt::from(j-5_i32)), order);
                    g_1_t_hat_h_tau = &g_1_t_hat_h_tau + &self.T_vec[j as usize] * Scalar::<Secp256k1>::from_bigint(&x_power);
                }
        
                assert_eq!(g_vec_L, g_vec_L_expect);
                if g_vec_L == g_vec_L_expect && g_1_t_hat_h_tau == g_1_t_hat_h_tau_expect {
                    Ok(())
                } else {
                    Err(RangeProofError)
                }
            }
            AgKnowledgeVec::IPA { t_hat, ip } => {
                let t_hat = Scalar::<Secp256k1>::from_bigint(t_hat);
                let g_1_t_hat_h_tau_expect = &g_vec[0] * t_hat.clone() + H * self.tau.clone();

                let mut g_1_t_hat_h_tau = Point::<Secp256k1>::zero();
                for j in 0..6 {
                    let x_power = BigInt::mod_pow(&challenge_x.to_bigint(), &(order - one.clone() + BigInt::from(j-6_i32)), order);
                    g_1_t_hat_h_tau = &g_1_t_hat_h_tau + &self.T_vec[j as usize] * Scalar::<Secp256k1>::from_bigint(&x_power);
                }
                for j in 6..16 {
                    let x_power = BigInt::mod_pow(&challenge_x.to_bigint(), &(BigInt::from(j-5_i32)), order);
                    g_1_t_hat_h_tau = &g_1_t_hat_h_tau + &self.T_vec[j as usize] * Scalar::<Secp256k1>::from_bigint(&x_power);
                }

                if g_1_t_hat_h_tau == g_1_t_hat_h_tau_expect {
                    let y_inv = y.clone().invert().unwrap();
                    let yi_inv = iterate(one_fe.clone(), |i| i.clone() * &y_inv)
                        .take(n*b+b_bar)
                        .collect::<Vec<Scalar<Secp256k1>>>();

                    let mut h_vec = (0..n*b+b_bar)
                        .map(|i| &g_vec[i] * yi_inv[i].clone())
                        .collect::<Vec<Point<Secp256k1>>>();

                    let x_neg_1 = BigInt::mod_pow(&challenge_x.to_bigint(), &(order - one.clone() - one.clone()), order);
                    let x_neg_2 = BigInt::mod_pow(&challenge_x.to_bigint(), &(order - one.clone() - two.clone()), order);
                    let x_2 = BigInt::mod_pow(&challenge_x.to_bigint(), &two, order);
                    let x_3 = BigInt::mod_pow(&challenge_x.to_bigint(), &BigInt::from(3), order);
                    let x_4 = BigInt::mod_pow(&challenge_x.to_bigint(), &BigInt::from(4), order);
                    let x_5 = BigInt::mod_pow(&challenge_x.to_bigint(), &BigInt::from(5), order);
                
                    let x_neg_2 = Scalar::<Secp256k1>::from_bigint(&x_neg_2);
                    let x_neg_1 = Scalar::<Secp256k1>::from_bigint(&x_neg_1);
                    let x_2 = Scalar::<Secp256k1>::from_bigint(&x_2);
                    let x_3 = Scalar::<Secp256k1>::from_bigint(&x_3);
                    let x_4 = Scalar::<Secp256k1>::from_bigint(&x_4);
                    let x_5 = Scalar::<Secp256k1>::from_bigint(&x_5);
                    let y_nb_plus_b_bar = Scalar::<Secp256k1>::from_bigint(&y_nb_plus_b_bar);
        
                    let mut P = &self.A * challenge_x.clone();
                    P = &P + &self.B * x_neg_1;
                    P = &P + &self.A_hat * y_nb_plus_b_bar * x_2;
                    P = &P + &self.B_hat * x_neg_2;
                    for j in 0..n+1 {
                        P = &P + &C_vec[j] * &x_3;
                        P = &P + &C_vec_hat[j] * &x_4;
                    }
                    P = &P + &self.D * x_5;
                    P = &P - H * self.rho.clone();
                    
                    let mut Q = h_vec.iter().zip(R).fold(Point::<Secp256k1>::zero(), |acc, x| {
                        if x.1 != BigInt::zero() {
                            let Ri = Scalar::<Secp256k1>::from(x.1);
                            let HRi: Point<Secp256k1> = x.0 * Ri * Scalar::<Secp256k1>::from(two.clone());
                            acc + &HRi
                        } else {
                            acc
                        }
                    });
                    Q = P.clone() + Q;

                    let kzen_label = seed + BigInt::from((n*b+b_bar) as u32);
                    let hash = Sha512::new().chain_bigint(&kzen_label).result_bigint();
                    let q = generate_random_point(&Converter::to_bytes(&hash));

                    transcript.append_points_array(b"g_vec", &g_vec);
                    transcript.append_points_array(b"h_vec", &h_vec);
                    let cx: Scalar<Secp256k1> = transcript.challenge_scalar(b"c");
                    let ux = &q * cx;

                    temp_vec = (0..n*b+b_bar)
                        .map(|i| BigInt::mod_mul(&(y_2_nb_plus_b_bar.clone() + y_3_nb_plus_b_bar.clone()), &yi[i].to_bigint(), order))
                        .collect::<Vec<BigInt>>();
                    let one_vec = vec![one.clone(); n*b+b_bar];

                    // pad
                    pad_point_to_power_of_two(&mut g_vec, &(seed + BigInt::from((n*b+b_bar+1) as u32)));
                    pad_point_to_power_of_two(&mut h_vec, &(seed + BigInt::from((n*b+b_bar+1+g_vec.len()) as u32)));

                    let z = BigInt::mod_add(&t_hat.to_bigint(), &(two.clone() * inner_product(&one_vec, &temp_vec, order)), order);
                    let result = ip.verify(transcript, &g_vec, &h_vec, &ux, &P, &(&Q + &ux * Scalar::<Secp256k1>::from_bigint(&z)));
                    if result.is_ok() {
                        Ok(())
                    } else {
                        Err(RangeProofError)
                    }
                } else {
                    Err(RangeProofError)
                }
            }
        }
    }

    pub fn prove(
        transcript: &mut Transcript,
        gi: &[Point<Secp256k1>],
        hi: &[Point<Secp256k1>],
        values: Vec<Scalar<Secp256k1>>,
        x_vec: Vec<Scalar<Secp256k1>>,
        s: Scalar<Secp256k1>,
        t: Scalar<Secp256k1>,
        n: usize,
        B_vec: &[Point<Secp256k1>],
        seed: &BigInt
    ) -> (SigmaPedersenProof, VarRange) {
        let sub_proof_1 = SigmaPedersenProof::prove(transcript, &values, &x_vec, gi, hi, B_vec, n+1);
        let sub_proof_2 = VarRange::range_prove(transcript, gi, hi, values, x_vec, s, t, n, B_vec, seed);
        (sub_proof_1, sub_proof_2)
    }

    pub fn verify(
        &self,
        transcript: &mut Transcript,
        sub_proof1: &SigmaPedersenProof,
        gi: &[Point<Secp256k1>],
        hi: &[Point<Secp256k1>],
        B_vec: &[Point<Secp256k1>],
        s: Scalar<Secp256k1>,
        t: Scalar<Secp256k1>,
        n: usize,
        seed: &BigInt
    ) -> Result<(), Errors> {
        let sub_res1 = sub_proof1.verify(transcript, B_vec, gi, hi, n+1);
        let sub_res2 = self.range_verify(transcript, gi, hi, B_vec, s, t, n, seed);
        if sub_res1.is_ok() && sub_res2.is_ok() {
            Ok(())
        } else {
            Err(VarRangeError)
        }
    }
}

#[cfg(test)]
mod test {
    use curv::{arithmetic::{Converter, Samplable}, cryptographic_primitives::hashing::DigestExt, elliptic::curves::{Point, Scalar, Secp256k1}, BigInt};
    use merlin::Transcript;
    use sha2::{Digest, Sha512};

    use super::{generate_random_point, VarRange};

    pub fn test_helper_range_proof(seed: &BigInt, s: Scalar<Secp256k1>, n: usize) {
        let gi = (0..n+1)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to gi:
        let hi = (0..n+1)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + seed;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let t = s.clone() * s.clone();

        let mut v_vec = (0..n)
            .map(|_| Scalar::<Secp256k1>::from_bigint(&BigInt::sample_below(&s.to_bigint())))
            .collect::<Vec<Scalar<Secp256k1>>>();
        v_vec.push(Scalar::<Secp256k1>::from_bigint(&BigInt::sample_below(&t.to_bigint())));

        let x_vec = (0..n+1)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let C_vec = (0..n+1)
            .map(|i| &gi[i] * v_vec[i].clone() + &hi[i] * x_vec[i].clone())
            .collect::<Vec<Point<Secp256k1>>>();

        let mut verifier = Transcript::new(b"rangeprooftest");
        let range_proof = VarRange::range_prove(&mut verifier, &gi, &hi, v_vec, x_vec, s.clone(), t.clone(), n, &C_vec, &(seed + BigInt::from((2*n+2) as i32)));
        let mut verifier = Transcript::new(b"rangeprooftest");
        let result = VarRange::range_verify(&range_proof, &mut verifier, &gi, &hi, &C_vec, s, t, n, &(seed + BigInt::from((2*n+2) as i32)));
        assert!(result.is_ok());
    }

    pub fn test_helper(seed: &BigInt, s: Scalar<Secp256k1>, n: usize) {
        let gi = (0..n+1)
            .map(|i| {
                let kzen_label_i = BigInt::from(i as u32) + seed;
                let hash_i = Sha512::new().chain_bigint(&kzen_label_i).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_i))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        // can run in parallel to gi:
        let hi = (0..n+1)
            .map(|i| {
                let kzen_label_j = BigInt::from(n as u32) + BigInt::from(i as u32) + seed;
                let hash_j = Sha512::new().chain_bigint(&kzen_label_j).result_bigint();
                generate_random_point(&Converter::to_bytes(&hash_j))
            })
            .collect::<Vec<Point<Secp256k1>>>();

        let t = s.clone() * s.clone();

        let mut v_vec = (0..n)
            .map(|_| Scalar::<Secp256k1>::from_bigint(&BigInt::sample_below(&s.to_bigint())))
            .collect::<Vec<Scalar<Secp256k1>>>();
        v_vec.push(Scalar::<Secp256k1>::from_bigint(&BigInt::sample_below(&t.to_bigint())));

        let x_vec = (0..n+1)
            .map(|_| Scalar::<Secp256k1>::random())
            .collect::<Vec<Scalar<Secp256k1>>>();

        let C_vec = (0..n+1)
            .map(|i| &gi[i] * v_vec[i].clone() + &hi[i] * x_vec[i].clone())
            .collect::<Vec<Point<Secp256k1>>>();
        
        let mut verifier = Transcript::new(b"varrangetest");
        let varrange_proof = VarRange::prove(&mut verifier, &gi, &hi, v_vec, x_vec, s.clone(), t.clone(), n, &C_vec, &(seed + BigInt::from((2*n+2) as i32)));
        let mut verifier = Transcript::new(b"varrangetest");
        let result = VarRange::verify(&varrange_proof.1, &mut verifier, &varrange_proof.0, &gi, &hi, &C_vec, s, t, n, &(seed + BigInt::from((2*n+2) as i32)));
        assert!(result.is_ok());
    }

    #[test]
    pub fn test_batch_4_varrange_proof_32() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper_range_proof(&kzen_label, Scalar::<Secp256k1>::from_bigint(&BigInt::from(32)), 4);
    }
    
    #[test]
    pub fn test_batch_4_varrange_proof_64() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper_range_proof(&kzen_label, Scalar::<Secp256k1>::from_bigint(&BigInt::from(64)), 4);
    }

    #[test]
    pub fn test_batch_4_varrange_proof_128() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper_range_proof(&kzen_label, Scalar::<Secp256k1>::from_bigint(&BigInt::from(128)), 4);
    }

    #[test]
    pub fn test_batch_4_varrange_proof_31() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper_range_proof(&kzen_label, Scalar::<Secp256k1>::from_bigint(&BigInt::from(31)), 4);
    }
    
    #[test]
    pub fn test_batch_4_varrange_proof_63() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper_range_proof(&kzen_label, Scalar::<Secp256k1>::from_bigint(&BigInt::from(63)), 4);
    }

    #[test]
    pub fn test_batch_4_varrange_proof_127() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper_range_proof(&kzen_label, Scalar::<Secp256k1>::from_bigint(&BigInt::from(127)), 4);
    }

    #[test]
    pub fn test_batch_4_varrange_31() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper(&kzen_label, Scalar::<Secp256k1>::from_bigint(&BigInt::from(31)), 4);
    }

    #[test]
    pub fn test_batch_4_varrange_63() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper(&kzen_label, Scalar::<Secp256k1>::from_bigint(&BigInt::from(63)), 4);
    }

    #[test]
    pub fn test_batch_4_varrange_127() {
        let KZen: &[u8] = &[75, 90, 101, 110];
        let kzen_label = BigInt::from_bytes(KZen);
        test_helper(&kzen_label, Scalar::<Secp256k1>::from_bigint(&BigInt::from(127)), 4);
    }
}