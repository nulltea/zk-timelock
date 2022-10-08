use crate::poseidon::get_poseidon_params;
use anyhow::anyhow;
use ark_ff::{to_bytes, BigInteger, BitIteratorLE, Field, PrimeField, ToConstraintField, Zero, Fp12, One, Fp6ParamsWrapper, Fp12ParamsWrapper, Fp2ParamsWrapper};
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
use group::Curve as _;

use ark_serialize::CanonicalDeserialize;
use ark_bls12_377::{G1Projective as Curve, Fq12Parameters, Fq, Fr, Fq12, Parameters as BlsParameters, Bls12_377, G1Projective, G2Affine};
use ark_bls12_381::Bls12_381;
//use ark_bls12_377::constraints::{G1Var, FqVar, Fq12Var};

// use ark_bls12_381::{G1Projective as Curve, Fq12Parameters, Fq, Fr, Fq12, Parameters as BlsParameters, Bls12_381 as Bls12_377, G1Projective, G2Affine};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::groups::curves::short_weierstrass::ProjectiveVar;
// use ark_bls12_377::constraints::{G1Var, FqVar, Fq12Var};

use crate::utils::{curve_scalar_mul_le, field_scalar_mul_le, from_compressed_bytes, g2_from_uncompressed_bytes, gt_to_fqs, gtvar_to_fqvars};
// use ark_bls12_381::{G1Projective as Curve, Fq12Parameters, Fq, Fr, Parameters as BlsParameters};
// type G1Var = ark_r1cs_std::groups::bls12::G1Var<BlsParameters>;

use sha2::Sha256;
use crate::nonnative::NonNativeAffineVar;

type G1Var = NonNativeAffineVar<ark_bls12_381::Parameters, ark_bls12_377::Fq>;
type FqVar = NonNativeFieldVar<ark_bls12_381::Fq, ark_bls12_377::Fq>;
type Fq2Var = ark_r1cs_std::fields::quadratic_extension::QuadExtVar<FqVar, Fp2ParamsWrapper<ark_bls12_381::Fq2Parameters>>;
type Fq6Var = ark_r1cs_std::fields::fp6_3over2::CubicExtVar<Fq2Var, Fp6ParamsWrapper<ark_bls12_381::Fq6Parameters>>;
type Fq12Var = ark_r1cs_std::fields::quadratic_extension::QuadExtVar<Fq6Var, Fp12ParamsWrapper<ark_bls12_381::Fq12Parameters>>;

pub struct EncryptCircuit
{
    gid: ark_bls12_381::Fq12,
    sigma: Randomness<ark_bls12_381::G1Projective>,
    master: PublicKey<Bls12_381>,
    msg: Plaintext<ark_bls12_381::G1Projective>,
    pub resulted_ciphertext: Ciphertext<ark_bls12_381::G1Projective>,
    params: Parameters<ark_bls12_377::G1Projective>,
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
pub struct  Ciphertext<C: ProjectiveCurve> {
    u: C,
    v: C::BaseField,
    w: C::BaseField,
}

impl EncryptCircuit
{
    pub fn new<I: AsRef<[u8]>, R: Rng + CryptoRng>(
        master: PublicKey<Bls12_381>,
        id: I,
        msg: Plaintext<ark_bls12_381::G1Projective>,
        rng: &mut R,
    ) -> anyhow::Result<Self> {
        let pp_381 = Parameters::<ark_bls12_381::G1Projective>::default();
        let pp_377 = Parameters::<ark_bls12_377::G1Projective>::default();

        let (gid, sigma, ct) = Self::encrypt_inner(&master, id, &msg, &pp_381, rng)
            .map_err(|e| anyhow!("error encrypting message: {e}"))?;

        Ok(Self {
            gid,
            sigma,
            msg,
            master,
            resulted_ciphertext: ct,
            params: pp_377,
        })
    }

    pub fn get_public_inputs(
        cipher: &Ciphertext<Curve>,
        params: &Parameters<Curve>,
    ) -> Vec<Fq>
    {
        let u_inputs = cipher.u.to_field_elements().unwrap();
        let v_inputs = cipher.v.to_field_elements().unwrap();
        let w_inputs = cipher.w.to_field_elements().unwrap();

        u_inputs.into_iter().chain(v_inputs).chain(w_inputs).collect()
    }

    pub fn encrypt<I: AsRef<[u8]>, R: Rng + CryptoRng>(
        master: &PublicKey<Bls12_381>,
        id: I,
        msg: &Plaintext<ark_bls12_381::G1Projective>,
        params: &Parameters<ark_bls12_381::G1Projective>,
        rng: &mut R,
    ) -> anyhow::Result<Ciphertext<ark_bls12_381::G1Projective>> {
        let (_, _, ct) = Self::encrypt_inner(master, id, msg, params, rng)?;
        Ok(ct)
    }

    fn encrypt_inner<I: AsRef<[u8]>, R: Rng + CryptoRng>(
        master: &PublicKey<Bls12_381>,
        id: I,
        msg: &Plaintext<ark_bls12_381::G1Projective>,
        params: &Parameters<ark_bls12_381::G1Projective>,
        rng: &mut R,
    ) -> anyhow::Result<(ark_bls12_381::Fq12, Randomness<ark_bls12_381::G1Projective>, Ciphertext<ark_bls12_381::G1Projective>)> {
        // 1. Compute Gid = e(master,Q_id)
        // Note: hash-to-curve algo is `draft-irtf-cfrg-bls-signature-05` which matches to the one used in Drand network,
        // hash function is Sha2 despite the fact that poseidon is used elsewhere to optimize proving performance.
        let gid = {
            let qid = bls12_381_plus::G2Projective::hash::<bls12_381_plus::ExpandMsgXmd<Sha256>>(id.as_ref(), tlock::ibe::H2C_DST)
                .to_affine();
            let qid = g2_from_uncompressed_bytes(&qid.to_uncompressed())?;
            Bls12_381::pairing(master.clone(), qid)
        };

        // 2. Derive random sigma
        let sigma = Randomness::<ark_bls12_381::G1Projective>::rand(rng);

        // 3. Derive r from sigma and msg
        let r = {
            let mut sponge = PoseidonSponge::new(&params.poseidon);
            sponge.absorb(&sigma.0);
            sponge.absorb(&msg);
            sponge.squeeze_field_elements::<ark_bls12_381::Fq>(1).remove(0)
        };

        // 4. Compute U = G*r
        let mut u = curve_scalar_mul_le(
            ark_bls12_381::G1Projective::prime_subgroup_generator(),
            r.into_repr().to_bytes_le()
        );

        // 5. Compute V = sigma XOR H(rGid)
        let v = {
            let mut r_gid: ark_bls12_381::Fq12 = field_scalar_mul_le(gid.clone(), r.into_repr().to_bytes_le());

            let mut sponge = PoseidonSponge::new(&params.poseidon);
            sponge.absorb(&gt_to_fqs(&r_gid));
            let h_r_gid = sponge.squeeze_field_elements::<ark_bls12_381::Fq>(1).remove(0);

            sigma.0 + h_r_gid
        };

        // 6. Compute W = M XOR H(sigma)
        let w = {
            // todo: could we skip hashing here?
            let mut sponge = PoseidonSponge::new(&params.poseidon);
            sponge.absorb(&sigma.0);
            let h_sigma = sponge.squeeze_field_elements::<ark_bls12_381::Fq>(1).remove(0);
            (*msg).clone() + h_sigma
        };

        Ok((gid, sigma, Ciphertext{
            u,
            v,
            w
        }))
    }

    // pub fn decrypt(
    //     sk: &SecretKey<Bls12_377>,
    //     ct: &Ciphertext<Curve>,
    //     params: &Parameters<Curve>,
    // ) -> anyhow::Result<Plaintext<Curve>> {
    //     // 1. Compute sigma = V XOR H2(e(rP,private))
    //     let sigma = {
    //         let r_gid = Bls12_377::pairing(ct.u.clone(), sk.clone());
    //         let mut sponge = PoseidonSponge::new(&params.poseidon);
    //         sponge.absorb(&gt_to_fqs(&r_gid));
    //         sponge.squeeze_field_elements::<Fq>(1).remove(0)
    //     };
    //
    //     // 2. Compute Msg = W XOR H4(sigma)
    //     let msg = {
    //         // todo: could we skip hashing here?
    //         let mut sponge = PoseidonSponge::new(&params.poseidon);
    //         sponge.absorb(&sigma);
    //         let h_sigma = sponge.squeeze_field_elements::<Fq>(1).remove(0);
    //         ct.w.clone() - h_sigma
    //     };
    //
    //     // 3. Check U = G^r
    //     let r_g = {
    //         let mut sponge = PoseidonSponge::new(&params.poseidon);
    //         sponge.absorb(&sigma);
    //         sponge.absorb(&msg);
    //         let r = sponge.squeeze_field_elements::<Fq>(1).remove(0);
    //         curve_scalar_mul_le(
    //             Curve::prime_subgroup_generator(),
    //             r.into_repr().to_bytes_le()
    //         )
    //     };
    //     assert_eq!(ct.u, r_g);
    //
    //     Ok(msg)
    // }

    pub(crate) fn verify_encryption(
        &self,
        cs: ConstraintSystemRef<Fq>,
        // gid: Fp12Var<Fq12Parameters>,
        msg: &FqVar,
        ct: &(G1Var, FqVar, FqVar),
    ) -> Result<(), SynthesisError> {
        let g_x = FqVar::new_constant(
            ns!(cs, "ciphertext_u_x"),
            &ark_bls12_381::G1Projective::prime_subgroup_generator().x
        )?;
        let g_y = FqVar::new_constant(
            ns!(cs, "ciphertext_u_x"),
            &ark_bls12_381::G1Projective::prime_subgroup_generator().y
        )?;
        let g = G1Var::new_variable(
            g_x, g_y
        );

        // 2. Derive random sigma
        let sigma = FqVar::new_witness(ns!(cs, "sigma"), || Ok(&self.sigma.0))?;


        // 3. Derive r from sigma and msg
        let r = {
            let mut sponge = PoseidonSpongeVar::new(cs.clone(), &self.params.poseidon);
            sponge.absorb(&sigma.to_constraint_field().unwrap())?;
            sponge.absorb(&msg.to_constraint_field().unwrap())?;
            sponge
                .squeeze_nonnative_field_elements::<ark_bls12_381::Fq>(1)
                .and_then(|r| Ok(r.0[0].clone()))?.to_bits_le()?
        };

        // 4. Compute U = G*r
        let u = g; //.scalar_mul_le(r.iter())?;
        u.enforce_equal(&ct.0)?;

        // 5. Compute V = sigma XOR H(rGid)
        // let v = {
        //     let r_gid = {
        //         let mut res = Fq12Var::new_constant(cs.clone(), &Fq12::zero())?;
        //         let mut mul = gid;
        //         for bit in r.into_iter() {
        //             let tmp = res.clone() + &mul;
        //             res = bit.select(&tmp, &res)?;
        //             mul.double_in_place()?;
        //         }
        //         res
        //     };
        //     let mut sponge = PoseidonSpongeVar::new(cs.clone(), &self.params.poseidon);
        //     // sponge.absorb(&gtvar_to_fqvars(&r_gid))?;
        //
        //     let h_r_gid = sponge
        //         .squeeze_field_elements(1)
        //         .and_then(|r| Ok(r[0].clone()))?;
        //
        //     &sigma + h_r_gid
        // };
        // v.enforce_equal(&ct.1)?;


        // 6. Compute W = M XOR H(sigma)
        let w = {
            let mut poseidon = PoseidonSpongeVar::new(cs.clone(), &self.params.poseidon);
            poseidon.absorb(&sigma.to_constraint_field().unwrap())?;
            let h_sigma = poseidon
                .squeeze_nonnative_field_elements::<ark_bls12_381::Fq>(1)
                .and_then(|r| Ok(r.0[0].clone()))?;

            msg + h_sigma
        };

        w.enforce_equal(&ct.2)?;

        Ok(())
    }

    pub(crate) fn ciphertext_var(
        &self,
        cs: ConstraintSystemRef<Fq>,
        mode: AllocationMode,
    ) -> Result<(G1Var, FqVar, FqVar), SynthesisError> {
        let u_x = FqVar::new_variable(
            ns!(cs, "ciphertext_u_x"),
            || {
                Ok(self.resulted_ciphertext.u.x)
            },
            mode,
        )?;
        let u_y = FqVar::new_variable(
            ns!(cs, "ciphertext_u_x"),
            || {
                Ok(self.resulted_ciphertext.u.y)
            },
            mode,
        )?;
        let u = G1Var::new_variable(
            u_x, u_y
        );

        let v = FqVar::new_variable(
            ns!(cs, "ciphertext_v"),
            || {
                Ok(self.resulted_ciphertext.v)
            },
            mode,
        )?;

        let w = FqVar::new_variable(
            ns!(cs, "ciphertext_w"),
            || {
                Ok(self.resulted_ciphertext.w)
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
        let message = FqVar::new_witness(ns!(cs, "plaintext"), || {
            Ok(self.msg)
        })?;
        let ciphertext = self.ciphertext_var(cs.clone(), AllocationMode::Input)?;

        self.verify_encryption(cs.clone(), /*gid,*/ &message, &ciphertext)
    }
}

#[cfg(test)]
mod tests {
    use ark_std::test_rng;
    use crate::poseidon;
    use super::*;

    use ark_bls12_377::{G1Projective as ProjectiveEngine, Fq, Fr, Fq12, G1Affine};
    // use ark_bls12_381::{G1Projective as ProjectiveEngine, Fq, Fr, Fq12, G1Affine, Bls12_381};
    use ark_bw6_761::BW6_761;
    use ark_ed_on_bls12_381::{EdwardsProjective, EdwardsParameters};

    use ark_ff::{Field, Zero};
    use ark_groth16::Groth16;
    use ark_serialize::CanonicalSerialize;

    use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
    use sha2::Digest;
    use crate::utils::{from_compressed_bytes, g1_from_uncompressed_bytes};

    #[test]
    fn test_decode() {
        let pk = {
            let bytes = hex::decode("8200fc249deb0148eb918d6e213980c5d01acd7fc251900d9260136da3b54836ce125172399ddc69c4e3e11429b62c11").unwrap();
            println!("{} {}", bytes.len(), hex::encode(&bytes));

            let x = bls12_381_plus::G1Affine::from_compressed((&*bytes).try_into().unwrap()).unwrap();

            g1_from_uncompressed_bytes(&x.to_uncompressed()).unwrap()
        };
    }

    // #[test]
    // fn test_decrypt() {
    //     let mut rng = test_rng();
    //     let bytes = [1, 2, 3];
    //     let msg = Fq::from_random_bytes(&bytes).unwrap();
    //
    //     let params = Parameters::<ProjectiveEngine> {
    //         poseidon: get_poseidon_params::<ProjectiveEngine>(2),
    //     };
    //     let pk = {
    //         let bytes = hex::decode("8200fc249deb0148eb918d6e213980c5d01acd7fc251900d9260136da3b54836ce125172399ddc69c4e3e11429b62c11").unwrap();
    //         let tmp = bls12_381_plus::G1Affine::from_compressed((&*bytes).try_into().unwrap()).unwrap();
    //
    //         g1_from_uncompressed_bytes(&tmp.to_uncompressed()).unwrap()
    //     };
    //     let sigma = Randomness::<G1Projective>::rand(&mut rng);
    //
    //     let round_number = 1000u64;
    //     let id = {
    //         let mut hash = sha2::Sha256::new();
    //         hash.update(&round_number.to_be_bytes());
    //         &hash.finalize().to_vec()[0..32]
    //     };
    //
    //     let ct = EncryptCircuit::encrypt(&pk, id, &msg, &params, &mut rng).unwrap();
    // }

    #[test]
    fn test_circuit() {
        let mut rng = test_rng();
        let bytes = [1, 2, 3];
        let msg = ark_bls12_381::Fq::from_random_bytes(&bytes).unwrap();

        let master: _ = {
            let bytes = hex::decode("8200fc249deb0148eb918d6e213980c5d01acd7fc251900d9260136da3b54836ce125172399ddc69c4e3e11429b62c11").unwrap();
            // g1_from_uncompressed_bytes(&bytes).unwrap()
            ark_bls12_381::G1Affine::prime_subgroup_generator()
        };
        let round_number = 1000u64;
        let id = {
            let mut hash = sha2::Sha256::new();
            hash.update(&round_number.to_be_bytes());
            &hash.finalize().to_vec()[0..32]
        };

        let circuit = EncryptCircuit::new(
            master.clone(),
            &id,
            msg.clone().into(),
            &mut rng,
        ).unwrap();

        let (pk, _vk) = Groth16::<BW6_761>::setup(circuit, &mut rng).unwrap();

        // let circuit = EncryptCircuit::new(master, id, msg.clone().into(), params.clone(), &mut rng).unwrap();
        // let ct = circuit.resulted_ciphertext.clone();
        // let _proof = Groth16::prove(&pk, circuit, &mut rng).unwrap();
    }
}
