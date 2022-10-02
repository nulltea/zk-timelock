use crate::poseidon::get_poseidon_params;
use anyhow::anyhow;
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::{to_bytes, BigInteger, BitIteratorLE, Field, PrimeField, ToConstraintField, Zero};
use ark_groth16::{Groth16, Proof, ProvingKey, VerifyingKey};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::groups::CurveVar;
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::ToConstraintFieldGadget;
use ark_relations::ns;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
};
use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_sponge::constraints::{AbsorbGadget, CryptographicSpongeVar};
use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_sponge::poseidon::{PoseidonParameters, PoseidonSponge};
use ark_sponge::{Absorb, CryptographicSponge, FieldBasedCryptographicSponge};
use ark_std::marker::PhantomData;
use ark_std::rand::{CryptoRng, Rng, RngCore};
use ark_std::vec::Vec;
use ark_std::UniformRand;
use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::str::FromStr;

pub struct EncryptCircuit<C, CV>
    where
        C: ProjectiveCurve,
        C::BaseField: PrimeField,
        CV: CurveVar<C, C::BaseField>,
{
    sigma: Randomness<C>,
    gid: PublicKey<C>,
    msg: Plaintext<C>,
    pub resulted_ciphertext: Ciphertext<C>,
    params: Parameters<C>,
    _curve_var: PhantomData<CV>,
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

pub type PublicKey<C> = C;

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

impl<C, CV> EncryptCircuit<C, CV>
    where
        C: ProjectiveCurve,
        C::BaseField: PrimeField,
        C::Affine: Absorb,
        C::BaseField: Absorb,
        CV: CurveVar<C, C::BaseField> + AbsorbGadget<C::BaseField>,
{
    pub fn new<R: Rng>(
        gid: PublicKey<C>,
        msg: Plaintext<C>,
        params: Parameters<C>,
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
            _curve_var: PhantomData,
        })
    }

    pub fn get_public_inputs<E: PairingEngine>(
        cipher: &Ciphertext<C>,
        params: &Parameters<C>,
    ) -> Vec<E::Fr>
        where
            C::BaseField: ToConstraintField<E::Fr>,
            C: ToConstraintField<E::Fr>,
    {
        let u_inputs = cipher.0.to_field_elements().unwrap();
        let v_inputs = cipher.1.to_field_elements().unwrap();
        let w_inputs = cipher.2.to_field_elements().unwrap();

        u_inputs.into_iter().chain(v_inputs).chain(w_inputs).collect()
    }

    pub fn encrypt(
        gid: &PublicKey<C>,
        msg: &Plaintext<C>,
        sigma: &Randomness<C>,
        params: &Parameters<C>,
    ) -> anyhow::Result<Ciphertext<C>> {
        // 3. Derive r from sigma and msg
        let r = {
            let mut sponge = PoseidonSponge::new(&params.poseidon);
            sponge.absorb(&sigma.0);
            sponge.absorb(&msg);
            sponge.squeeze_field_elements::<C::ScalarField>(1).remove(0)
        };

        // 4. Compute U = G*r
        let mut u = C::prime_subgroup_generator();
        u.mul_assign(r.clone());

        // 5. Compute V = sigma XOR H(rGid)
        let v = {
            let mut sponge = PoseidonSponge::new(&params.poseidon);
            let mut r_gid = gid.clone();
            r_gid.mul_assign(r);
            sponge.absorb(&sigma.0);
            sponge.absorb(&msg);
            let h_r_gid = sponge.squeeze_field_elements::<C::BaseField>(1).remove(0);

            sigma.0 + h_r_gid
        };

        // 6. Compute W = M XOR H(sigma)
        let w = {
            let mut sponge = PoseidonSponge::new(&params.poseidon);
            sponge.absorb(&sigma.0);
            let h_sigma = sponge.squeeze_field_elements::<C::BaseField>(1).remove(0);
            msg.clone() + h_sigma
        };

        Ok((u, v, w))
    }

    pub(crate) fn verify_encryption(
        &self,
        cs: ConstraintSystemRef<C::BaseField>,
        gid: &CV,
        plaintext: &FpVar<C::BaseField>,
        ciphertext: &(CV, FpVar<C::BaseField>, FpVar<C::BaseField>),
    ) -> Result<(), SynthesisError> {
        let g = CV::new_constant(ns!(cs, "generator"), C::prime_subgroup_generator())?;

        // 2. Derive random sigma
        let sigma = {
            let bytes = to_bytes![&self.sigma.0].unwrap();
            UInt8::new_witness_vec(ns!(cs, "sigma"), &bytes)?
                .iter()
                .flat_map(|b| b.to_bits_le().unwrap())
                .collect::<Vec<_>>()
        };

        // 3. Derive r from sigma and msg
        let r = {
            let mut poseidon = PoseidonSpongeVar::new(cs.clone(), &self.params.poseidon);
            poseidon.absorb(&sigma)?;
            poseidon.absorb(&plaintext)?;
            poseidon
                .squeeze_field_elements(1)
                .and_then(|r| Ok(r[0].clone()))?
        };

        // 4. Compute U = G*r
        let u = g.clone().scalar_mul_le(sigma.iter())?;
        u.enforce_equal(&ciphertext.0)?;

        // 5. Compute V = sigma XOR H(rGid)
        // let v = {
        //     let r_gid = gid.clone().scalar_mul_le(randomness.iter())?;
        //     let mut poseidon = PoseidonSpongeVar::new(cs.clone(), &self.params.poseidon);
        //     poseidon.absorb(&r_gid)?;
        //     let h_r_gid = poseidon
        //         .squeeze_field_elements(1)
        //         .and_then(|r| Ok(r[0].clone()))?;
        // };

        // 6. Compute W = M XOR H(sigma)
        let w = {
            let mut poseidon = PoseidonSpongeVar::new(cs.clone(), &self.params.poseidon);
            poseidon.absorb(&sigma)?;
            let h_sigma = poseidon
                .squeeze_field_elements(1)
                .and_then(|r| Ok(r[0].clone()))?;

            plaintext + h_sigma
        };

        w.enforce_equal(&ciphertext.2)?;

        Ok(())
    }

    pub(crate) fn ciphertext_var(
        &self,
        cs: ConstraintSystemRef<C::BaseField>,
        mode: AllocationMode,
    ) -> Result<(CV, FpVar<C::BaseField>, FpVar<C::BaseField>), SynthesisError> {
        let u = CV::new_variable(
            ns!(cs, "ciphertext_u"),
            || Ok(self.resulted_ciphertext.0),
            mode,
        )?;
        let v = FpVar::<C::BaseField>::new_variable(
            ns!(cs, "ciphertext_v"),
            || {
                Ok(self.resulted_ciphertext.1)
            },
            mode,
        )?;

        let w = FpVar::<C::BaseField>::new_variable(
            ns!(cs, "ciphertext_w"),
            || {
                Ok(self.resulted_ciphertext.2)
            },
            mode,
        )?;

        Ok((u, v, w))
    }
}

impl<C, CV> ConstraintSynthesizer<C::BaseField> for EncryptCircuit<C, CV>
    where
        C: ProjectiveCurve,
        C::BaseField: PrimeField,
        C::Affine: Absorb,
        C::BaseField: Absorb,
        CV: CurveVar<C, C::BaseField> + AllocVar<C, C::BaseField> + AbsorbGadget<C::BaseField>,
{
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<C::BaseField>,
    ) -> Result<(), SynthesisError> {
        let gid = CV::new_input(ns!(cs, "gid"), || Ok(self.gid))?;
        let message = FpVar::<C::BaseField>::new_witness(ns!(cs, "plaintext"), || {
            Ok(self.msg)
        })?;
        let ciphertext = self.ciphertext_var(cs.clone(), AllocationMode::Input)?;

        self.verify_encryption(cs.clone(), &gid, &message, &ciphertext)
    }
}
