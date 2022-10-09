use anyhow::anyhow;
use ark_ec::{bls12, PairingEngine, ProjectiveCurve, SWModelParameters};
use ark_ec::bls12::Bls12Parameters;
use ark_ec::short_weierstrass_jacobian::GroupAffine;
use ark_ff::{BigInteger256, BigInteger384, Field, Zero};
use ark_r1cs_std::fields::fp12::Fp12Var;
use ark_r1cs_std::fields::fp::FpVar;
use ark_serialize::{CanonicalDeserialize, SerializationError};
use group::Curve;
use sha2::Sha256;

pub trait Hash2Curve: Sized {
    fn hash(msg: &[u8], dst: &[u8]) -> anyhow::Result<Self>;
}

impl Hash2Curve for ark_bls12_381::G2Affine where Self: ZkCryptoDeserialize {
    fn hash(msg: &[u8], dst: &[u8]) -> anyhow::Result<Self> {
        let qid = bls12_381_plus::G2Projective::hash::<bls12_381_plus::ExpandMsgXmd<Sha256>>(msg, dst)
            .to_affine();
        Self::deserialize_zk_crypto(&qid.to_uncompressed())
    }
}

pub trait ZkCryptoDeserialize: Sized {
    fn deserialize_zk_crypto(bytes: &[u8]) -> anyhow::Result<Self>;
}

impl ZkCryptoDeserialize for GroupAffine<ark_bls12_381::g1::Parameters> {
    fn deserialize_zk_crypto(bytes: &[u8]) -> anyhow::Result<Self> {
        let x = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[0..48]);

            // Mask away the flag bits
            tmp[0] &= 0b0001_1111;

            let x = bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0;
            ark_bls12_381::Fq::from(BigInteger384(x))
        };

        // Attempt to obtain the y-coordinate
        let y = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[48..96]);

            ark_bls12_381::Fq::from(BigInteger384(bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0))
        };

        Ok(ark_bls12_381::G1Affine::new(x, y, false))
    }
}

impl ZkCryptoDeserialize for GroupAffine<ark_bls12_381::g2::Parameters> {
    fn deserialize_zk_crypto(bytes: &[u8]) -> anyhow::Result<Self> {
        let xc0 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[0..48]);

            // Mask away the flag bits
            tmp[0] &= 0b0001_1111;

            ark_bls12_381::Fq::from(BigInteger384::new(bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0))
        };

        let xc1 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[48..96]);

            // Mask away the flag bits
            tmp[0] &= 0b0001_1111;

            ark_bls12_381::Fq::from(BigInteger384::new(bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0))
        };

        // Attempt to obtain the y-coordinate
        let yc0 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[96..144]);

            ark_bls12_381::Fq::from(BigInteger384::new(bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0))
        };
        let yc1 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[144..192]);

            ark_bls12_381::Fq::from(BigInteger384::new(bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0))
        };

        Ok(ark_bls12_381::G2Affine::new(
            ark_bls12_381::Fq2::new(xc0, xc1),
            ark_bls12_381::Fq2::new(yc0, yc1),
            false,
        ))
    }
}


pub fn field_scalar_mul_le<T: Field + Zero, B: AsRef<[u8]>>(trg: T, rhs: B) -> T {
    let mut res = T::zero();
    let mut mul = trg;
    // This is a simple double-and-add implementation of group element
    // multiplication, moving from most significant to least
    // significant bit of the scalar.
    //
    // We skip the leading bit because it's always unset for Fq
    // elements.
    for bit in rhs
        .as_ref()
        .iter()
        .rev()
        .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1u8) == 1u8))
        .skip(1)
    {
        res = res.double();
        if bit {
            res = res.add(&mul)
        }
    }
    res
}

pub fn curve_scalar_mul_le<T: ProjectiveCurve + Zero, B: AsRef<[u8]>>(trg: T, rhs: B) -> T {
    let mut res = T::zero();
    let mut mul = trg;

    for bit in rhs
        .as_ref()
        .iter()
        .rev()
        .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1u8) == 1u8))
        .skip(1)
    {
        res = res.double();
        if bit {
            res = res.add(&mul)
        }
    }
    res
}

pub trait GtAbsorbable: PairingEngine {
    fn gt_to_absorbable(gt: &Self::Fqk) -> Vec<Self::Fq>;
}

impl GtAbsorbable for ark_bls12_381::Bls12_381 {
    fn gt_to_absorbable(gt: &ark_bls12_381::Fq12) -> Vec<ark_bls12_381::Fq> {
        vec![
            gt.c0.c0.c0,
            gt.c0.c0.c1,
            gt.c0.c1.c0,
            gt.c0.c1.c1,
            gt.c0.c2.c0,
            gt.c0.c2.c1,
            gt.c1.c0.c0,
            gt.c1.c0.c1,
            gt.c1.c1.c0,
            gt.c1.c1.c1,
            gt.c1.c2.c0,
            gt.c1.c2.c1,
        ]
    }
}

impl GtAbsorbable for ark_bls12_377::Bls12_377 {
    fn gt_to_absorbable(gt: &ark_bls12_377::Fq12) -> Vec<ark_bls12_377::Fq> {
        vec![
            gt.c0.c0.c0,
            gt.c0.c0.c1,
            gt.c0.c1.c0,
            gt.c0.c1.c1,
            gt.c0.c2.c0,
            gt.c0.c2.c1,
            gt.c1.c0.c0,
            gt.c1.c0.c1,
            gt.c1.c1.c0,
            gt.c1.c1.c1,
            gt.c1.c2.c0,
            gt.c1.c2.c1,
        ]
    }
}

pub fn gtvar_to_fqvars<E: PairingEngine, P: Bls12Parameters<Fp = E::Fq>>(gt: &Fp12Var<P::Fp12Params>) -> Vec<&FpVar<E::Fq>> {
    return vec![
        &gt.c0.c0.c0,
        &gt.c0.c0.c1,
        &gt.c0.c1.c0,
        &gt.c0.c1.c1,
        &gt.c0.c2.c0,
        &gt.c0.c2.c1,
        &gt.c1.c0.c0,
        &gt.c1.c0.c1,
        &gt.c1.c1.c0,
        &gt.c1.c1.c1,
        &gt.c1.c2.c0,
        &gt.c1.c2.c1,
    ]
}

#[cfg(test)]
mod tests {
    use ark_std::test_rng;
    use super::*;

    #[test]
    fn test_decode() {
        let pk = {
            let bytes = hex::decode("8200fc249deb0148eb918d6e213980c5d01acd7fc251900d9260136da3b54836ce125172399ddc69c4e3e11429b62c11").unwrap();

            let g1 = ark_bls12_381::G1Affine::deserialize_zk_crypto(&bytes).unwrap();

        };
    }
}
