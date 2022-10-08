use anyhow::anyhow;
use ark_bls12_377::{Fq, Fq12, G1Affine};
use ark_bls12_377::constraints::{Fq12Var, FqVar};
use ark_ec::{ProjectiveCurve, SWModelParameters};
use ark_ec::short_weierstrass_jacobian::GroupAffine;
use ark_ff::{BigInteger256, BigInteger384, Field, Zero};
use ark_serialize::{CanonicalDeserialize, SerializationError};

pub fn from_compressed_bytes<T: CanonicalDeserialize>(bytes: &[u8]) -> anyhow::Result<T> {
    let mut reader = ark_std::io::BufReader::new(bytes);

    T::deserialize_unchecked(&mut reader).map_err(|e| anyhow!("deserialization error: {e}"))
}


pub fn g1_from_uncompressed_bytes(bytes: &[u8]) -> anyhow::Result<ark_bls12_381::G1Affine> {
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

pub fn g2_from_uncompressed_bytes(bytes: &[u8]) -> anyhow::Result<ark_bls12_381::G2Affine> {
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

pub fn gt_to_fqs(gt: &ark_bls12_381::Fq12) -> Vec<ark_bls12_381::Fq> {
    return vec![
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

pub fn gtvar_to_fqvars(gt: &Fq12Var) -> Vec<&FqVar> {
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
