use ark_ec::pairing::{MillerLoopOutput, PairingOutput};
use ark_ec::{models::short_weierstrass::SWCurveConfig, pairing::Pairing};
use ark_ff::{
    biginteger::BigInt,
    fields::{BitIteratorBE, Field},
    CyclotomicMultSubgroup, One,
};
use itertools::Itertools;

use crate::yata_127::{Fq, Fq3, Fq6, Fr};

pub mod g1;
pub use self::g1::{G1Affine, G1Prepared, G1Projective};

pub mod g2;
pub use self::g2::{G2Affine, G2Prepared, G2Projective};

#[cfg(test)]
mod tests;

pub type GT = Fq6;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Yata;

impl Pairing for Yata {
    type ScalarField = Fr;
    type G1 = G1Projective;
    type G1Affine = G1Affine;
    type G1Prepared = G1Prepared;
    type G2 = G2Projective;
    type G2Affine = G2Affine;
    type G2Prepared = G2Prepared;
    type TargetField = Fq6;

    fn multi_miller_loop(
        a: impl IntoIterator<Item = impl Into<Self::G1Prepared>>,
        b: impl IntoIterator<Item = impl Into<Self::G2Prepared>>,
    ) -> MillerLoopOutput<Self> {
        let mut result = Self::TargetField::one();
        a.into_iter().zip_eq(b).for_each(|(p, q)| {
            let (p, q) = (p.into(), q.into());
            result *= &Yata::ate_miller_loop(&p.0, &q.0);
        });

        MillerLoopOutput(result)
    }

    fn final_exponentiation(r: MillerLoopOutput<Self>) -> Option<PairingOutput<Self>> {
        Some(PairingOutput(Yata::final_exponentiation(&r.0)))
    }
}

impl Yata {
    pub fn ate_pairing(p: &G1Affine, q: &G2Affine) -> GT {
        Yata::final_exponentiation(&Yata::ate_miller_loop(p, q))
    }

    fn ate_miller_loop(p: &G1Affine, q: &G2Affine) -> GT {
        let px = p.x;
        let py = p.y;
        let qx = q.x;
        let qy = q.y;
        let mut py_twist_squared = TWIST.square();
        py_twist_squared.mul_assign_by_fp(&py);

        let mut old_rx;
        let mut old_ry;
        let mut rx = qx;
        let mut ry = qy;
        let mut f = Fq6::one();

        // The for loop is executed for all bits (EXCEPT the MSB itself) of
        // cp6_782_param_p (skipping leading zeros) in MSB to LSB order
        for bit in BitIteratorBE::without_leading_zeros(ATE_LOOP_COUNT).skip(1) {
            old_rx = rx;
            old_ry = ry;

            let old_rx_square = old_rx.square();
            let old_rx_square_3 = old_rx_square.double() + &old_rx_square;
            let old_rx_square_3_a = old_rx_square_3 + &g2::Parameters::COEFF_A;
            let old_ry_double_inverse = old_ry.double().inverse().unwrap();

            let gamma = old_rx_square_3_a * &old_ry_double_inverse;
            let gamma_twist = gamma * &TWIST;
            let gamma_old_rx = gamma * &old_rx;
            let mut gamma_twist_px = gamma_twist;
            gamma_twist_px.mul_assign_by_fp(&px);

            let x = py_twist_squared;
            let y = gamma_old_rx - &old_ry - &gamma_twist_px;
            let ell_rr_at_p: Fq6 = Fq6::new(x, y);

            rx = gamma.square() - &old_rx.double();
            ry = gamma * &(old_rx - &rx) - &old_ry;
            f = f.square() * &ell_rr_at_p;

            if bit {
                old_rx = rx;
                old_ry = ry;

                let gamma = (old_ry - &qy) * &((old_rx - &qx).inverse().unwrap());
                let gamma_twist = gamma * &TWIST;
                let gamma_qx = gamma * &qx;
                let mut gamma_twist_px = gamma_twist;
                gamma_twist_px.mul_assign_by_fp(&px);

                let x = py_twist_squared;
                let y = gamma_qx - &qy - &gamma_twist_px;
                let ell_rq_at_p: Fq6 = Fq6::new(x, y);

                rx = gamma.square() - &old_rx - &qx;
                ry = gamma * &(old_rx - &rx) - &old_ry;
                f = f * &ell_rq_at_p;
            }
        }
        f
    }

    fn final_exponentiation(value: &Fq6) -> GT {
        let value_inv = value.inverse().unwrap();
        let value_to_first_chunk = Yata::final_exponentiation_first(value, &value_inv);
        let value_inv_to_first_chunk = Yata::final_exponentiation_first(&value_inv, value);
        Yata::final_exponentiation_last(&value_to_first_chunk, &value_inv_to_first_chunk)
    }

    fn final_exponentiation_first(elt: &Fq6, elt_inv: &Fq6) -> Fq6 {
        // (q^3-1)*(q+1)

        // elt_q3 = elt^(q^3)
        let mut elt_q3 = elt.clone();
        elt_q3.frobenius_map(3);
        // elt_q3_over_elt = elt^(q^3-1)
        let elt_q3_over_elt = elt_q3 * elt_inv;
        // alpha = elt^((q^3-1) * q)
        let mut alpha = elt_q3_over_elt.clone();
        alpha.frobenius_map(1);
        // beta = elt^((q^3-1)*(q+1)
        alpha * &elt_q3_over_elt
    }

    fn final_exponentiation_last(elt: &Fq6, elt_inv: &Fq6) -> Fq6 {
        let mut elt_q = elt.clone();
        elt_q.frobenius_map(1);

        let w1_part = elt_q.cyclotomic_exp(&FINAL_EXPONENT_LAST_CHUNK_W1);
        let w0_part = if FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG {
            elt_inv.cyclotomic_exp(&FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0)
        } else {
            elt.cyclotomic_exp(&FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0)
        };

        w1_part * &w0_part
    }
}

/// TWIST = (0, 1, 0)
pub const TWIST: Fq3 = Fq3::new(Fq::ZERO, Fq::ONE, Fq::ZERO);

/// ATE_IS_LOOP_COUNT_NEG = false
pub const ATE_IS_LOOP_COUNT_NEG: bool = false;

/// ATE_LOOP_COUNT =
/// 34380436325771620967632952473828082793156904272317916245459108005096274242451447298267646534317268794665575692661797924110338
pub const ATE_LOOP_COUNT: [u64; 7] = [
    0xb7f85555fffc0002,
    0x54cbd80711fbffff,
    0x6bccfd2cd0893dcb,
    0x29a59332c81ec5e7,
    0x89a9a647060e78ee,
    0x5d096e709bb66ad9,
    0x340223d5
];

/// FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG = true
pub const FINAL_EXPONENT_LAST_CHUNK_W0_IS_NEG: bool = false;

/// FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0 =
/// 58583714044779100235452016811134025443672948020624341127823350194447647092441447238950014466895323216352825557141173068490572165842429050707090738457799985646421001926066877381067472193649462839618834773106665601731187657924804573
pub const FINAL_EXPONENT_LAST_CHUNK_ABS_OF_W0: BigInt<12> = BigInt::new([
    0x2c8600160025ffdd,
    0x5524f008621f9ae3,
    0xd24f8e521a7c5570,
    0xe2b8c65023544060,
    0xb68a2657b3a688f1,
    0xb5079fce52c4e019,
    0x8396269ad9beffe8,
    0xd244f87c5edd7abe,
    0x4b655e2a84d659d1,
    0xe20ce9133ee928d7,
    0x0e66c5f20b2d9af4,
    0x9a8fa3c4d416760
]);

/// FINAL_EXPONENT_LAST_CHUNK_W1 =
/// 600746357873917083993205832519317177466334726496174638989123538389804293458724181786507272967556
pub const FINAL_EXPONENT_LAST_CHUNK_W1: BigInt<12> = BigInt::new([
    0xc5dd0009ffeb0016,
    0x82fe84651c1426c0,
    0x01da78c4aa5145a7,
    0x06b99b6f27d67048,
    0x538abe7d2db06ef7,
    0x1ad7c04a13d851cd,
    0x1a0111eb238987dc,
    0x0,
    0x0,
    0x0,
    0x0,
    0x0,
]);
