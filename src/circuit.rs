use crate::poseidon::get_poseidon_params;
use anyhow::anyhow;
use ark_ff::{to_bytes, BigInteger, BitIteratorLE, Field, PrimeField, ToConstraintField, Zero, Fp12, One};
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::ToConstraintFieldGadget;
use ark_relations::ns;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
};
use ark_r1cs_std::groups::CurveVar;
use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_sponge::poseidon::{PoseidonParameters, PoseidonSponge};
use ark_std::marker::PhantomData;
use ark_std::rand::{CryptoRng, Rng, RngCore};
use ark_std::vec::Vec;
use ark_std::UniformRand;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::ops::{Add, Mul, MulAssign};
use std::str::FromStr;
use ark_ec::bls12::Bls12Parameters;
use ark_r1cs_std::fields::fp12::Fp12Var;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::CryptographicSponge;
// use ark_ed_on_bls12_381::{EdwardsProjective as Curve, Fr, Fq, EdwardsParameters as BlsParameters};
// use ark_ed_on_bls12_381::constraints::{EdwardsVar as G1Var};


use ark_bls12_377::{G1Projective as Curve, Fq12Parameters, Fq, Fr, Fq12, Parameters as BlsParameters, constraints::{G1Var, Fq12Var}, Bls12_377};
use ark_bls12_377::constraints::FqVar;
use crate::utils::{curve_scalar_mul_le, field_scalar_mul_le};
// use ark_bls12_381::{G1Projective as Curve, Fq12Parameters, Fq, Fr, Parameters as BlsParameters};
// type G1Var = ark_r1cs_std::groups::bls12::G1Var<BlsParameters>;


pub struct EncryptCircuit
{
    sigma: Randomness<Curve>,
    gid: PublicKey<Bls12_377>,
    msg: Plaintext<Curve>,
    pub resulted_ciphertext: Ciphertext<Curve>,
    params: Parameters<Curve>,
}

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
        <C::BaseField as FromStr>::Err: Debug,
{
    fn default() -> Self {
        Self {
            poseidon: get_poseidon_params::<C>(2),
        }
    }
}

pub type PublicKey<E: PairingEngine> = E::Fqk;

pub type SecretKey<C: ProjectiveCurve> = C::ScalarField;

pub struct Randomness<C: ProjectiveCurve>(pub C::BaseField);

impl<C: ProjectiveCurve> UniformRand for Randomness<C> {
    #[inline]
    fn rand<R: Rng + ?Sized>(rng: &mut R) -> Self {
        Randomness(<C as ProjectiveCurve>::BaseField::rand(rng))
    }
}

pub type Plaintext<C: ProjectiveCurve> = C::BaseField;

pub type Ciphertext<C: ProjectiveCurve> = (C, C::BaseField, C::BaseField);

impl EncryptCircuit
{
    pub fn new<R: Rng>(
        gid: PublicKey<Bls12_377>,
        msg: Plaintext<Curve>,
        params: Parameters<Curve>,
        rnd: &mut R,
    ) -> anyhow::Result<Self> {
        let r = Randomness::rand(rnd);

        let enc = Self::encrypt(&gid, &msg, &r, &params)
            .map_err(|e| anyhow!("error encrypting message: {e}"))?;

        Ok(Self {
            sigma: r,
            msg,
            gid,
            resulted_ciphertext: enc,
            params,
        })
    }

    pub fn get_public_inputs(
        cipher: &Ciphertext<Curve>,
        params: &Parameters<Curve>,
    ) -> Vec<Fq>
    {
        let u_inputs = cipher.0.to_field_elements().unwrap();
        let v_inputs = cipher.1.to_field_elements().unwrap();
        let w_inputs = cipher.2.to_field_elements().unwrap();

        u_inputs.into_iter().chain(v_inputs).chain(w_inputs).collect()
    }

    pub fn encrypt(
        gid: &PublicKey<Bls12_377>,
        msg: &Plaintext<Curve>,
        sigma: &Randomness<Curve>,
        params: &Parameters<Curve>,
    ) -> anyhow::Result<Ciphertext<Curve>> {
        // 3. Derive r from sigma and msg
        let r = {
            let mut sponge = PoseidonSponge::new(&params.poseidon);
            sponge.absorb(&sigma.0);
            sponge.absorb(&msg);
            sponge.squeeze_field_elements::<Fq>(1).remove(0)
        };

        // 4. Compute U = G*r
        let mut u = curve_scalar_mul_le(
            Curve::prime_subgroup_generator(),
            r.into_repr().to_bytes_le()
        );

        // 5. Compute V = sigma XOR H(rGid)
        let v = {
            let mut sponge = PoseidonSponge::new(&params.poseidon);
            let mut r_gid: Fq12 = field_scalar_mul_le((*gid).clone(), r.into_repr().to_bytes_le());

            sponge.absorb(&r_gid.c0.c0.c0);
            sponge.absorb(&r_gid.c0.c0.c1);
            sponge.absorb(&r_gid.c0.c1.c0);
            sponge.absorb(&r_gid.c0.c1.c1);
            sponge.absorb(&r_gid.c0.c2.c0);
            sponge.absorb(&r_gid.c0.c2.c1);
            sponge.absorb(&r_gid.c1.c0.c0);
            sponge.absorb(&r_gid.c1.c0.c1);
            sponge.absorb(&r_gid.c1.c1.c0);
            sponge.absorb(&r_gid.c1.c1.c1);
            sponge.absorb(&r_gid.c1.c2.c0);
            sponge.absorb(&r_gid.c1.c2.c1);

            let h_r_gid = sponge.squeeze_field_elements::<Fq>(1).remove(0);

            sigma.0 + h_r_gid
        };

        // 6. Compute W = M XOR H(sigma)
        let w = {
            let mut sponge = PoseidonSponge::new(&params.poseidon);
            sponge.absorb(&sigma.0);
            let h_sigma = sponge.squeeze_field_elements::<Fq>(1).remove(0);
            h_sigma
        };

        Ok((u, v, w))
    }

    pub(crate) fn verify_encryption(
        &self,
        cs: ConstraintSystemRef<Fq>,
        gid: Fp12Var<Fq12Parameters>,
        plaintext: &FpVar<Fq>,
        ciphertext: &(G1Var, FpVar<Fq>, FpVar<Fq>),
    ) -> Result<(), SynthesisError> {
        let g = G1Var::new_constant(ns!(cs, "generator"), Curve::prime_subgroup_generator())?;

        // 2. Derive random sigma
        let sigma = FqVar::new_witness(ns!(cs, "sigma"), || Ok(&self.sigma.0))?;


        // 3. Derive r from sigma and msg
        let r = {
            let mut sponge = PoseidonSpongeVar::new(cs.clone(), &self.params.poseidon);
            sponge.absorb(&sigma)?;
            sponge.absorb(&plaintext)?;
            sponge
                .squeeze_field_elements(1)
                .and_then(|r| Ok(r[0].clone()))?.to_bits_le()?
        };

        // 4. Compute U = G*r
        let u = g.clone().scalar_mul_le(r.iter())?;
        u.enforce_equal(&ciphertext.0)?;

        // 5. Compute V = sigma XOR H(rGid)
        let v = {
            let r_gid = {
                let mut res = Fq12Var::new_constant(cs.clone(), &Fq12::zero())?;
                let mut mul = gid;
                for bit in r.into_iter() {
                    let tmp = res.clone() + &mul;
                    res = bit.select(&tmp, &res)?;
                    mul.double_in_place()?;
                }
                res
            };
            let mut sponge = PoseidonSpongeVar::new(cs.clone(), &self.params.poseidon);
            sponge.absorb(&r_gid.c0.c0.c0)?;
            sponge.absorb(&r_gid.c0.c0.c1)?;
            sponge.absorb(&r_gid.c0.c1.c0)?;
            sponge.absorb(&r_gid.c0.c1.c1)?;
            sponge.absorb(&r_gid.c0.c2.c0)?;
            sponge.absorb(&r_gid.c0.c2.c1)?;
            sponge.absorb(&r_gid.c1.c0.c0)?;
            sponge.absorb(&r_gid.c1.c0.c1)?;
            sponge.absorb(&r_gid.c1.c1.c0)?;
            sponge.absorb(&r_gid.c1.c1.c1)?;
            sponge.absorb(&r_gid.c1.c2.c0)?;
            sponge.absorb(&r_gid.c1.c2.c1)?;
            let h_r_gid = sponge
                .squeeze_field_elements(1)
                .and_then(|r| Ok(r[0].clone()))?;

            &sigma + h_r_gid
        };
        v.enforce_equal(&ciphertext.1)?;


        // 6. Compute W = M XOR H(sigma)
        let w = {
            let mut poseidon = PoseidonSpongeVar::new(cs.clone(), &self.params.poseidon);
            poseidon.absorb(&sigma)?;
            let h_sigma = poseidon
                .squeeze_field_elements(1)
                .and_then(|r| Ok(r[0].clone()))?;

            h_sigma
        };

        w.enforce_equal(&ciphertext.2)?;

        Ok(())
    }

    pub(crate) fn ciphertext_var(
        &self,
        cs: ConstraintSystemRef<Fq>,
        mode: AllocationMode,
    ) -> Result<(G1Var, FpVar<Fq>, FpVar<Fq>), SynthesisError> {
        let u = G1Var::new_variable(
            ns!(cs, "ciphertext_u"),
            || Ok(self.resulted_ciphertext.0),
            mode,
        )?;
        let v = FpVar::<Fq>::new_variable(
            ns!(cs, "ciphertext_v"),
            || {
                Ok(self.resulted_ciphertext.1)
            },
            mode,
        )?;

        let w = FpVar::<Fq>::new_variable(
            ns!(cs, "ciphertext_w"),
            || {
                Ok(self.resulted_ciphertext.2)
            },
            mode,
        )?;

        Ok((u, v, w))
    }
}

impl ConstraintSynthesizer<Fq> for EncryptCircuit
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<Fq>,
    ) -> Result<(), SynthesisError> {

        let gid = Fq12Var::new_input(ns!(cs, "gid"), || Ok(self.gid))?;
        //let gid = G1Var::new_input(ns!(cs, "gid"), || Ok(self.gid))?;
        let message = FpVar::<Fq>::new_witness(ns!(cs, "plaintext"), || {
            Ok(self.msg)
        })?;
        let ciphertext = self.ciphertext_var(cs.clone(), AllocationMode::Input)?;

        self.verify_encryption(cs.clone(), gid, &message, &ciphertext)
    }
}
