use anyhow::anyhow;
use ark_ec::ProjectiveCurve;
use ark_ff::{Field, Zero};
use ark_serialize::CanonicalDeserialize;

pub fn from_compressed_bytes<T: CanonicalDeserialize>(bytes: &[u8]) -> anyhow::Result<T> {
    let mut reader = ark_std::io::BufReader::new(bytes);

    T::deserialize_uncompressed(&mut reader).map_err(|e| anyhow!("deserialization error: {e}"))
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
