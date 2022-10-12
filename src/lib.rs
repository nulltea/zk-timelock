#![feature(inherent_associated_types)]

pub mod circuit;
mod parameters;
pub mod poseidon;
pub mod utils;
mod nonnative;
pub mod yata_127;

pub use crate::circuit::*;

pub use ark_bls12_381::Bls12_381;
use ark_ec::{CurveGroup};
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_sponge::poseidon::PoseidonConfig;
use ark_std::rand::Rng;
use ark_std::UniformRand;
use crate::poseidon::get_poseidon_params;

#[derive(Clone, Debug)]
pub struct Parameters<C: CurveGroup>
    where
        C::BaseField: PrimeField,
{
    pub poseidon: PoseidonConfig<C::BaseField>,
}

impl<C: CurveGroup> Default for Parameters<C>
    where
        C::BaseField: PrimeField,
{
    fn default() -> Self {
        Self {
            poseidon: get_poseidon_params::<C>(2),
        }
    }
}

pub type PublicKey<E: Pairing> = E::G1Affine;

pub type SecretKey<E: Pairing> = E::G2Affine;

pub struct Randomness<C: CurveGroup>(pub C::BaseField);

impl<C: CurveGroup> UniformRand for Randomness<C> {
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Randomness(<C as CurveGroup>::BaseField::rand(rng))
    }
}

pub type Plaintext<C: CurveGroup> = C::BaseField;

#[derive(Clone, Debug)]
pub struct Ciphertext<C: CurveGroup> {
    u: C,
    v: C::BaseField,
    w: C::BaseField,
}
