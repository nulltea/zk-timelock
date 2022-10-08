use std::ops::{Add, AddAssign};
use ark_ec::bls12::Bls12Parameters;
use ark_ec::group::Group;
use ark_ff::{Field, One, PrimeField, Zero};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::{FieldOpsBounds, FieldVar};
use ark_relations::r1cs::SynthesisError;

#[derive(Clone)]
pub struct NonNativeAffineVar<P: Bls12Parameters, CF: PrimeField>
    where
        P::Fp: PrimeField,
{
    x: NonNativeFieldVar<P::Fp, CF>,
    y: NonNativeFieldVar<P::Fp, CF>,
    z: NonNativeFieldVar<P::Fp, CF>,
}

impl<P: Bls12Parameters, CF: PrimeField> NonNativeAffineVar<P, CF>
    where
        P::Fp: PrimeField,
{
    pub fn new_variable(
        x: NonNativeFieldVar<P::Fp, CF>,
        y: NonNativeFieldVar<P::Fp, CF>,
    ) -> Self {
        Self { x, y, z: NonNativeFieldVar::Constant(P::Fp::zero()) }
    }
}

impl<P: Bls12Parameters, CF: PrimeField> Add<&Self> for NonNativeAffineVar<P, CF>
    where
        P::Fp: PrimeField,
{
    type Output = Self;

    fn add(mut self, other: &Self) -> Self::Output {
        self += other;
        self
    }
}

impl<'a, P: Bls12Parameters, CF: PrimeField> AddAssign<&'a Self> for NonNativeAffineVar<P, CF>
    where
        P::Fp: PrimeField,
{
    fn add_assign(&mut self, other: &'a Self) {
        // if self.is_zero() {
        //     *self = *other;
        //     return;
        // }
        //
        // if other.is_zero() {
        //     return;
        // }

        // http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
        // Works for all curves.

        // Z1Z1 = Z1^2
        let z1z1 = self.z.square().unwrap();

        // Z2Z2 = Z2^2
        let z2z2 = other.z.square().unwrap();

        // U1 = X1*Z2Z2
        let u1 = &self.x * &z2z2;

        // U2 = X2*Z1Z1
        let u2 = &other.x * &z1z1;

        // S1 = Y1*Z2*Z2Z2
        let s1 = &self.y * &other.z * &z2z2;

        // S2 = Y2*Z1*Z1Z1
        let s2 = &other.y * &self.z * &z1z1;

        if u1 == u2 && s1 == s2 {
            // The two points are equal, so we double.
            //self.double_in_place();
        } else {
            // If we're adding -a and a together, self.z becomes zero as H becomes zero.

            // H = U2-U1
            let h = u2 - &u1;

            // I = (2*H)^2
            let i = (h.double().unwrap()).square().unwrap();

            // J = H*I
            let j = &h * &i;

            // r = 2*(S2-S1)
            let r = (s2 - &s1).double().unwrap();

            // V = U1*I
            let v = u1 * &i;

            // X3 = r^2 - J - 2*V
            self.x = r.square().unwrap() - &j - &(v.double().unwrap());

            // Y3 = r*(V - X3) - 2*S1*J
            self.y = r * &(v - &self.x) - &*(s1 * &j).double_in_place().unwrap();

            // Z3 = ((Z1+Z2)^2 - Z1Z1 - Z2Z2)*H
            self.z = ((&self.z + &other.z).square().unwrap() - &z1z1 - &z2z2) * &h;
        }
    }
}


impl<P: Bls12Parameters, CF: PrimeField> EqGadget<CF> for NonNativeAffineVar<P, CF>
    where
        P::Fp: PrimeField,
{
    fn is_eq(&self, other: &Self) -> Result<Boolean<CF>, SynthesisError> {
        let is_x_eq = self.x.is_eq(&other.x)?;
        let is_y_eq = self.y.is_eq(&other.y)?;
        is_x_eq.and(&is_y_eq)
    }
}

