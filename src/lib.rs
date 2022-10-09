pub mod circuit;
mod parameters;
pub mod poseidon;
pub mod utils;
mod nonnative;

pub use crate::circuit::*;

pub use ark_bls12_381::Bls12_381;
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::PrimeField;
use ark_sponge::poseidon::PoseidonParameters;
use ark_std::rand::Rng;
use ark_std::UniformRand;
use crate::poseidon::get_poseidon_params;

#[derive(Clone, Debug)]
pub struct Parameters<C: ProjectiveCurve>
    where
        C::BaseField: PrimeField,
{
    pub poseidon: PoseidonParameters<C::BaseField>,
}

impl<C: ProjectiveCurve> Default for Parameters<C>
    where
        C::BaseField: PrimeField,
{
    fn default() -> Self {
        Self {
            poseidon: get_poseidon_params::<C>(2),
        }
    }
}

pub type PublicKey<E: PairingEngine> = E::G1Affine;

pub type SecretKey<E: PairingEngine> = E::G2Affine;

pub struct Randomness<C: ProjectiveCurve>(pub C::BaseField);

impl<C: ProjectiveCurve> UniformRand for Randomness<C> {
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Randomness(<C as ProjectiveCurve>::BaseField::rand(rng))
    }
}

pub type Plaintext<C: ProjectiveCurve> = C::BaseField;

#[derive(Clone, Debug)]
pub struct Ciphertext<C: ProjectiveCurve> {
    u: C,
    v: C::BaseField,
    w: C::BaseField,
}
