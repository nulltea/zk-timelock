use anyhow::anyhow;
use ark_bls12_377::Bls12_377;
use ark_bls12_381::Bls12_381;
use ark_ec::{bls12, CurveGroup, AffineRepr};
use ark_ec::bls12::Bls12Parameters;
use ark_ec::pairing::Pairing;
use ark_ec::short_weierstrass::Affine;
use ark_ff::{BigInteger, BigInteger256, BigInteger384, Field, PrimeField, QuadExtField, Zero};
use ark_r1cs_std::fields::fp12::Fp12Var;
use ark_r1cs_std::fields::fp::FpVar;
use ark_serialize::{CanonicalDeserialize, SerializationError};
use group::Curve;
use sha2::Sha256;

pub trait Hash2Curve: Pairing {
    fn hash(msg: &[u8], dst: &[u8]) -> anyhow::Result<Self::G2Affine>;
}

impl Hash2Curve for Bls12_381 where Self::G2Affine: ZkCryptoDeserialize {
    fn hash(msg: &[u8], dst: &[u8]) -> anyhow::Result<Self::G2Affine> {
        let qid = bls12_381_plus::G2Projective::hash::<bls12_381_plus::ExpandMsgXmd<Sha256>>(msg, dst)
            .to_affine();
        Self::G2Affine::deserialize_zk_crypto_uncompressed(&qid.to_uncompressed())
    }
}

impl Hash2Curve for Bls12_377 {
    fn hash(msg: &[u8], dst: &[u8]) -> anyhow::Result<Self::G2Affine> {
        Ok(Self::G2Affine::generator())
    }
}

pub trait ZkCryptoDeserialize: Sized {
    fn deserialize_zk_crypto(bytes: &[u8]) -> anyhow::Result<Self>;
    fn deserialize_zk_crypto_uncompressed(bytes: &[u8]) -> anyhow::Result<Self>;
}

impl ZkCryptoDeserialize for Affine<ark_bls12_381::g1::Parameters> {
    fn deserialize_zk_crypto(bytes: &[u8]) -> anyhow::Result<Self> {
        let g1 = bls12_381_plus::G1Affine::from_compressed(bytes.try_into().unwrap()).unwrap();
        let bytes = g1.to_uncompressed();

        Self::deserialize_zk_crypto_uncompressed(&bytes)
    }

    fn deserialize_zk_crypto_uncompressed(bytes: &[u8]) -> anyhow::Result<Self> {
        let x = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[0..48]);

            // Mask away the flag bits
            tmp[0] &= 0b0001_1111;

            let mut x= ark_bls12_381::Fq::zero();
            x.0.0 = bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0;
            x
        };

        // Attempt to obtain the y-coordinate
        let y = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[48..96]);

            let mut y= ark_bls12_381::Fq::zero();
            y.0.0 = bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0;
            y
        };

        Ok(ark_bls12_381::G1Affine::new(x, y))
    }
}

impl ZkCryptoDeserialize for Affine<ark_bls12_381::g2::Parameters> {
    fn deserialize_zk_crypto(bytes: &[u8]) -> anyhow::Result<Self> {
        let g2 = bls12_381_plus::G2Affine::from_compressed(bytes.try_into().unwrap()).unwrap();
        let bytes = g2.to_uncompressed();

        Self::deserialize_zk_crypto_uncompressed(&bytes)
    }

    fn deserialize_zk_crypto_uncompressed(bytes: &[u8]) -> anyhow::Result<Self> {
        let xc1 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[0..48]);

            // Mask away the flag bits
            tmp[0] &= 0b0001_1111;

            let mut f = ark_bls12_381::Fq::zero();
            f.0.0 = bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0;
            f
        };

        let xc0 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[48..96]);

            let mut f = ark_bls12_381::Fq::zero();
            f.0.0 = bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0;
            f
        };

        // Attempt to obtain the y-coordinate
        let yc1 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[96..144]);

            let mut f = ark_bls12_381::Fq::zero();
            f.0.0 = bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0;
            f
        };
        let yc0 = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[144..192]);

            let mut f = ark_bls12_381::Fq::zero();
            f.0.0 = bls12_381_plus::fp::Fp::from_bytes(&tmp).unwrap().0;
            f
        };

        Ok(ark_bls12_381::G2Affine::new(
            ark_bls12_381::Fq2::new(xc0, xc1),
            ark_bls12_381::Fq2::new(yc0, yc1),
        ))
    }
}

pub fn gt_scalar_mul_le<T: Field + Zero, B: AsRef<[u8]>>(trg: T, rhs: B) -> T {
    let mut res = T::one();
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
    {
        res.square_in_place();
        if bit {
            res *= mul;
        }
    }
    res
}

pub fn curve_scalar_mul_le<T: CurveGroup + Zero, B: AsRef<[u8]>>(trg: T, rhs: B) -> T {
    let mut res = T::zero();
    let mut mul = trg;

    for bit in rhs
        .as_ref()
        .iter()
        .rev()
        .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1u8) == 1u8))
    {
        res.double_in_place();
        if bit {
            res += mul;
        }
    }
    res
}

pub trait GtAbsorbable: Pairing {
    fn gt_to_absorbable(gt: &Self::TargetField) -> Vec<<Self::G1 as CurveGroup>::BaseField>;
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

pub fn gtvar_to_fqvars<E: Pairing, P: Bls12Parameters<Fp = <E::G1 as CurveGroup>::BaseField>>(gt: &Fp12Var<P::Fp12Config>) -> Vec<&FpVar<<E::G1 as CurveGroup>::BaseField>>
    where <E::G1 as CurveGroup>::BaseField: PrimeField{
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
