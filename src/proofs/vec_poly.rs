#![allow(non_snake_case)]

use curv::BigInt;
use curv::arithmetic::traits::*;
use std::ops::{Add, Mul};

#[derive(Clone)]
pub struct VecPoly{
    coeffs: Vec<Vec<BigInt>>,
    modulus: BigInt,
    offset: i32
}

impl VecPoly {
    pub fn new(coeffs: Vec<Vec<BigInt>>, modulus: BigInt, offset: i32) -> Self {
        VecPoly { coeffs, modulus, offset }
    }

    pub fn evaluate(&self, x: &BigInt) -> Vec<BigInt> {
        let n = self.coeffs[0].len();
        let mut out = vec![BigInt::zero(); n];

        let mut x_power = vec![BigInt::zero(); self.coeffs.len()];
        for i in 0..x_power.len() {
            let mut exp = BigInt::from(i as i32 - self.offset);
            if exp < BigInt::zero() {
                exp = exp + self.modulus.clone() - BigInt::one();
            }
            x_power[i] = BigInt::mod_pow(x, &exp, &self.modulus);
        }

        for i in 0..n {
            for j in 0..self.coeffs.len() {
                out[i] = BigInt::mod_add(
                    &out[i],
                    &BigInt::mod_mul(&self.coeffs[j][i], &x_power[j], &self.modulus),
                    &self.modulus
                );
            }
        }
        out
    }

}

impl Add for VecPoly {
    type Output = VecPoly;

    fn add(self, other: VecPoly) -> VecPoly {
        assert_eq!(self.modulus, other.modulus);
        assert_eq!(self.coeffs.len(), other.coeffs.len());
        assert_eq!(self.coeffs[0].len(), other.coeffs[0].len());
        assert_eq!(self.offset, other.offset);
        
        let mut new_coeffs = Vec::with_capacity(self.coeffs.len());
        for (coeff_vec1, coeff_vec2) in self.coeffs.into_iter().zip(other.coeffs) {
            let mut new_coeff_vec = Vec::with_capacity(coeff_vec1.len());
            for (coeff1, coeff2) in coeff_vec1.into_iter().zip(coeff_vec2) {
                let sum = BigInt::mod_add(&coeff1, &coeff2, &self.modulus);
                new_coeff_vec.push(sum);
            }
            new_coeffs.push(new_coeff_vec);
        }
        VecPoly::new(new_coeffs, self.modulus, self.offset)
    }
}

impl Mul for VecPoly {
    type Output = Vec<BigInt>;

    fn mul(self, other: VecPoly) -> Vec<BigInt> {
        assert_eq!(self.modulus, other.modulus);
        assert_eq!(self.coeffs[0].len(), other.coeffs[0].len());
        assert_eq!(self.offset, other.offset);

        let mut result_coeffs = vec![BigInt::zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, coeff_vec1) in self.coeffs.iter().enumerate() {
            for (j, coeff_vec2) in other.coeffs.iter().enumerate() {
                result_coeffs[i + j] = BigInt::mod_add(&result_coeffs[i + j], &inner_product(coeff_vec1, coeff_vec2, &self.modulus), &self.modulus);
            }
        }
        result_coeffs
    }
}

pub fn inner_product(a: &[BigInt], b: &[BigInt], modulus: &BigInt) -> BigInt {
    assert_eq!(
        a.len(),
        b.len(),
        "inner_product(a,b): lengths of vectors do not match"
    );
    let out = BigInt::zero();
    let out = a.iter().zip(b).fold(out, |acc, x| {
        let aibi = BigInt::mod_mul(x.0, x.1, modulus);
        BigInt::mod_add(&acc, &aibi, modulus)
    });
    out
}

#[cfg(test)]
mod tests {
    use curv::arithmetic::{One, Zero};
    use curv::BigInt;
    use super::VecPoly;

    pub fn test_helper_evaluate_vec_poly(L: VecPoly, x: BigInt) {
        let res = L.evaluate(&x);
        for val in res {
            print!("{} ", val);
        }
    }

    pub fn test_helper_mul_vec_poly(L: VecPoly, R: VecPoly) {
        let res = L * R;
        for coeff in res {
            print!("{} ", coeff);
        }
    }

    #[test]
    pub fn test_vec_poly() {
        let mut coeff1: Vec<Vec<BigInt>> = Vec::new();

        let row0 = vec![BigInt::zero(); 4];
        let row1 = vec![BigInt::one(); 4];

        coeff1.push(row0.clone());
        coeff1.push(row0.clone());
        coeff1.push(row1.clone());
        coeff1.push(row1.clone());
        coeff1.push(row0.clone());
        coeff1.push(row1.clone());
        coeff1.push(row1.clone());
        coeff1.push(row1.clone());
        coeff1.push(row1.clone());
        coeff1.push(row1.clone());

        let mut coeff2: Vec<Vec<BigInt>> = Vec::new();

        coeff2.push(row1.clone());
        coeff2.push(row1.clone());
        coeff2.push(row1.clone());
        coeff2.push(row1.clone());
        coeff2.push(row0.clone());
        coeff2.push(row0.clone());
        coeff2.push(row1.clone());

        let L = VecPoly::new(coeff1, BigInt::from(65537), 4);
        let R = VecPoly::new(coeff2, BigInt::from(65537), 4);

        test_helper_evaluate_vec_poly(L.clone(), BigInt::from(2));

        test_helper_mul_vec_poly(L.clone(), R);

    }

}


