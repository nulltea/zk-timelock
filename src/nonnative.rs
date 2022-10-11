use std::borrow::Borrow;
use std::marker::PhantomData;
use std::ops::{Add, AddAssign};
use ark_ec::{bls12, SWModelParameters};
use ark_ec::bls12::Bls12Parameters;
use ark_ec::group::Group;
use ark_ff::{Field, Fp12, Fp12Parameters, Fp2Parameters, One, PrimeField, QuadExtField, QuadExtParameters, Zero};
use ark_nonnative_field::NonNativeFieldVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::{FieldOpsBounds, FieldVar};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::quadratic_extension::QuadExtVarParams;
use ark_r1cs_std::prelude::{AllocationMode, AllocVar, CondSelectGadget, UInt8};
use ark_r1cs_std::{R1CSVar, ToConstraintFieldGadget};
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::constraints::AbsorbGadget;

pub type G1Var<CF> = NonNativeAffineVar<ark_bls12_381::g1::Parameters, CF>;
pub type FqVar<CF> = NonNativeFieldVar<ark_bls12_381::Fq, CF>;
pub type Fq2Var<CF> = Fp2Var<ark_bls12_381::Fq, CF>;
pub type Fq6Var<CF> = Fp6Var<ark_bls12_381::Fq, CF>;
pub type Fq12Var<CF> = Fp12Var<ark_bls12_381::Fq, CF>;

#[derive(Clone, Debug)]
pub struct NonNativeAffineVar<P: SWModelParameters, CF: PrimeField>
    where P::BaseField: PrimeField
{
    x: NonNativeFieldVar<P::BaseField, CF>,
    y: NonNativeFieldVar<P::BaseField, CF>,
    z: NonNativeFieldVar<P::BaseField, CF>,
}

impl<P: SWModelParameters + Clone, CF: PrimeField> NonNativeAffineVar<P, CF>
    where P::BaseField: PrimeField
{
    pub fn new(
        x: NonNativeFieldVar<P::BaseField, CF>,
        y: NonNativeFieldVar<P::BaseField, CF>,
    ) -> Self {
        Self::new_inner(x, y, NonNativeFieldVar::one())
    }

    fn new_inner(
        x: NonNativeFieldVar<P::BaseField, CF>,
        y: NonNativeFieldVar<P::BaseField, CF>,
        z: NonNativeFieldVar<P::BaseField, CF>,
    ) -> Self {
        Self { x, y, z: NonNativeFieldVar::one() }
    }

    fn zero() -> Self {
        Self::new_inner(NonNativeFieldVar::zero(), NonNativeFieldVar::one(), NonNativeFieldVar::one())
    }

    fn is_zero(&self) -> Result<Boolean<CF>, SynthesisError> {
        self.z.is_zero()
    }

    pub fn scalar_mul_le<'a>(
        &self,
        bits: impl Iterator<Item = &'a Boolean<CF>>,
    ) -> Result<Self, SynthesisError> {
        let mut res = Self::zero();
        let mut mul = Self::new(self.x.clone(), self.y.clone());

        for bit in bits {
            let tmp = res.clone() + &mul;
            res = bit.select(&tmp, &res)?;
            mul.double_in_place()?;
        }
        Ok(res)
    }

    pub(crate) fn double(&self) -> Result<Self, SynthesisError> {
        Ok(self.clone().add(&self))
    }

    fn double_in_place(&mut self) -> Result<(), SynthesisError> {
        *self = self.double()?;
        Ok(())
    }
}

fn mul_by_coeff_a<
    P: SWModelParameters,
    CF: PrimeField
>(
    f: &NonNativeFieldVar<P::BaseField, CF>,
) -> NonNativeFieldVar<P::BaseField, CF>
    where P::BaseField: PrimeField
{
    if !P::COEFF_A.is_zero() {
        f * P::COEFF_A
    } else {
        NonNativeFieldVar::<P::BaseField, CF>::zero()
    }
}

impl<P: SWModelParameters + Clone, CF: PrimeField> Add<&Self> for NonNativeAffineVar<P, CF>
    where P::BaseField: PrimeField
{
    type Output = Self;

    fn add(mut self, other: &Self) -> Self::Output {
        // Complete addition formula from Renes-Costello-Batina 2015
        // Algorithm 1
        // (https://eprint.iacr.org/2015/1060).
        // Below, comments at the end of a line denote the corresponding
        // step(s) of the algorithm
        //
        // Adapted from code in
        // https://github.com/RustCrypto/elliptic-curves/blob/master/p256/src/arithmetic/projective.rs
        let three_b = P::COEFF_B.double() + &P::COEFF_B;
        let (x1, y1, z1) = (&self.x, &self.y, &self.z);
        let (x2, y2, z2) = (&other.x, &other.y, &other.z);

        let xx = x1 * x2; // 1
        let yy = y1 * y2; // 2
        let zz = z1 * z2; // 3
        let xy_pairs = ((x1 + y1) * &(x2 + y2)) - (&xx + &yy); // 4, 5, 6, 7, 8
        let xz_pairs = ((x1 + z1) * &(x2 + z2)) - (&xx + &zz); // 9, 10, 11, 12, 13
        let yz_pairs = ((y1 + z1) * &(y2 + z2)) - (&yy + &zz); // 14, 15, 16, 17, 18

        let axz = mul_by_coeff_a::<P, CF>(&xz_pairs); // 19

        let bzz3_part = &axz + &zz * three_b; // 20, 21

        let yy_m_bzz3 = &yy - &bzz3_part; // 22
        let yy_p_bzz3 = &yy + &bzz3_part; // 23

        let azz = mul_by_coeff_a::<P, CF>(&zz);
        let xx3_p_azz = xx.double().unwrap() + &xx + &azz; // 25, 26, 27, 29

        let bxz3 = &xz_pairs * three_b; // 28
        let b3_xz_pairs = mul_by_coeff_a::<P, CF>(&(&xx - &azz)) + &bxz3; // 30, 31, 32

        let x = (&yy_m_bzz3 * &xy_pairs) - &yz_pairs * &b3_xz_pairs; // 35, 39, 40
        let y = (&yy_p_bzz3 * &yy_m_bzz3) + &xx3_p_azz * b3_xz_pairs; // 24, 36, 37, 38
        let z = (&yy_p_bzz3 * &yz_pairs) + xy_pairs * xx3_p_azz; // 41, 42, 43

        Self::new_inner(x, y, z)
    }
}


impl<P: SWModelParameters, CF: PrimeField> EqGadget<CF> for NonNativeAffineVar<P, CF>
    where P::BaseField: PrimeField
{
    fn is_eq(&self, other: &Self) -> Result<Boolean<CF>, SynthesisError> {
        let is_x_eq = self.x.is_eq(&other.x)?;
        let is_y_eq = self.y.is_eq(&other.y)?;
        is_x_eq.and(&is_y_eq)
    }
}

impl<P: SWModelParameters + Clone, CF: PrimeField> CondSelectGadget<CF> for NonNativeAffineVar<P, CF>
    where P::BaseField: PrimeField
{
    fn conditionally_select(
        cond: &Boolean<CF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let x = NonNativeFieldVar::<P::BaseField, CF>::conditionally_select(
            cond,
            &true_value.x,
            &false_value.x,
        )?;
        let y = NonNativeFieldVar::<P::BaseField, CF>::conditionally_select(
            cond,
            &true_value.x,
            &false_value.x,
        )?;

        Ok(NonNativeAffineVar::<P, CF>::new(x, y))
    }
}

#[derive(Clone, Debug)]
pub struct Fp2Var<T: PrimeField, B: PrimeField>
{
    /// The zero-th coefficient of this field element.
    pub c0: NonNativeFieldVar<T, B>,
    /// The first coefficient of this field element.
    pub c1: NonNativeFieldVar<T, B>,
}


impl<T: PrimeField, B: PrimeField> Fp2Var<T, B>
{
    pub fn new(c0: NonNativeFieldVar<T, B>, c1: NonNativeFieldVar<T, B>) -> Self {
        Self {
            c0,
            c1,
        }
    }

    fn zero() -> Self {
        let c0 = NonNativeFieldVar::<T, B>::zero();
        let c1 = NonNativeFieldVar::<T, B>::zero();
        Self::new(c0, c1)
    }

    fn one() -> Self {
        let c0 = NonNativeFieldVar::<T, B>::one();
        let c1 = NonNativeFieldVar::<T, B>::zero();
        Self::new(c0, c1)
    }

    fn double(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.double()?;
        let c1 = self.c1.double()?;
        Ok(Self::new(c0, c1))
    }

    fn square(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.square()?;
        let c1 = self.c1.square()?;
        Ok(Self::new(c0, c1))
    }

    fn add(&self, other: &Self) -> Self {
        let mut c0 = &self.c0 + &other.c0;
        let mut c1 = &self.c1 + &other.c1;
        Fp2Var::new(c0, c1)
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut c0 = &self.c0 * &other.c0;
        let mut c1 = &self.c1 * &other.c1;
        Self::new(c0, c1)
    }
}

impl<TF: PrimeField, BF: PrimeField> CondSelectGadget<BF> for Fp2Var<TF, BF>
{
    fn conditionally_select(
        cond: &Boolean<BF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let c0 = NonNativeFieldVar::<TF, BF>::conditionally_select(
            cond,
            &true_value.c0,
            &false_value.c0,
        )?;
        let c1 = NonNativeFieldVar::<TF, BF>::conditionally_select(
            cond,
            &true_value.c1,
            &false_value.c1,
        )?;

        Ok(Self::new(c0, c1))
    }
}

#[derive(Clone, Debug)]
pub struct Fp6Var<T: PrimeField, B: PrimeField>
{
    /// The zero-th coefficient of this field element.
    pub c0: Fp2Var<T, B>,
    /// The first coefficient of this field element.
    pub c1: Fp2Var<T, B>,
    /// The second coefficient of this field element.
    pub c2: Fp2Var<T, B>,
}

impl<T: PrimeField, B: PrimeField> Fp6Var<T, B>
{
    pub fn new(c0: Fp2Var<T, B>, c1: Fp2Var<T, B>, c2: Fp2Var<T, B>) -> Self {
        Self {
            c0,
            c1,
            c2,
        }
    }

    fn zero() -> Self {
        let c0 = Fp2Var::<T, B>::zero();
        let c1 = Fp2Var::<T, B>::zero();
        let c2 = Fp2Var::<T, B>::zero();
        Self::new(c0, c1, c2)
    }

    fn one() -> Self {
        let c0 = Fp2Var::<T, B>::one();
        let c1 = Fp2Var::<T, B>::zero();
        let c2 = Fp2Var::<T, B>::zero();
        Self::new(c0, c1, c2)
    }

    fn double(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.double()?;
        let c1 = self.c1.double()?;
        let c2 = self.c2.double()?;
        Ok(Self::new(c0, c1, c2))
    }

    fn square(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.square()?;
        let c1 = self.c1.square()?;
        let c2 = self.c2.square()?;
        Ok(Self::new(c0, c1, c2))
    }

    fn add(&self, other: &Self) -> Self {
        let mut c0 = self.c0.add(&other.c0);
        let mut c1 = self.c1.add(&other.c1);
        let mut c2 = self.c2.add(&other.c2);
        Self::new(c0, c1, c2)
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut c0 = self.c0.mul(&other.c0);
        let mut c1 = self.c1.mul(&other.c1);
        let mut c2 = self.c2.mul(&other.c2);
        Self::new(c0, c1, c2)
    }
}

impl<TF: PrimeField, BF: PrimeField> CondSelectGadget<BF> for Fp6Var<TF, BF>
{
    fn conditionally_select(
        cond: &Boolean<BF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let c0 = Fp2Var::<TF, BF>::conditionally_select(
            cond,
            &true_value.c0,
            &false_value.c0,
        )?;
        let c1 = Fp2Var::<TF, BF>::conditionally_select(
            cond,
            &true_value.c1,
            &false_value.c1,
        )?;
        let c2 = Fp2Var::<TF, BF>::conditionally_select(
            cond,
            &true_value.c2,
            &false_value.c2,
        )?;

        Ok(Self::new(c0, c1, c2))
    }
}


#[derive(Clone, Debug)]
pub struct Fp12Var<T: PrimeField, B: PrimeField>
{
    /// The zero-th coefficient of this field element.
    pub c0: Fp6Var<T, B>,
    /// The first coefficient of this field element.
    pub c1: Fp6Var<T, B>,
}


impl<T: PrimeField, B: PrimeField> Fp12Var<T, B>
{
    pub fn new(c0: Fp6Var<T, B>, c1: Fp6Var<T, B>) -> Self {
        Self {
            c0,
            c1,
        }
    }

    pub fn zero() -> Self {
        let c0 = Fp6Var::<T, B>::zero();
        let c1 = Fp6Var::<T, B>::zero();
        Self::new(c0, c1)
    }

    pub fn one() -> Self {
        let c0 = Fp6Var::<T, B>::one();
        let c1 = Fp6Var::<T, B>::zero();
        Self::new(c0, c1)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    pub fn double(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.double()?;
        let c1 = self.c1.double()?;
        Ok(Self::new(c0, c1))
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    fn square(&self) -> Result<Self, SynthesisError> {
        let c0 = self.c0.square()?;
        let c1 = self.c1.square()?;
        Ok(Self::new(c0, c1))
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    pub(crate) fn double_in_place(&mut self) -> Result<(), SynthesisError> {
        *self = self.double()?;
        Ok(())
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    pub(crate) fn square_in_place(&mut self) -> Result<(), SynthesisError> {
        *self = self.square()?;
        Ok(())
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    pub fn add(&self, other: &Self) -> Self {
        let mut c0 = self.c0.add(&other.c0);
        let mut c1 = self.c1.add(&other.c1);
        Self::new(c0, c1)
    }

    #[tracing::instrument(target = "r1cs", skip(self))]
    pub fn mul(&self, other: &Self) -> Self {
        let mut c0 = self.c0.mul(&other.c0);
        let mut c1 = self.c1.mul(&other.c1);
        Self::new(c0, c1)
    }

    #[tracing::instrument(target = "r1cs", skip(bits))]
    pub fn scalar_mul_le<'a>(
        &self,
        bits: impl Iterator<Item = &'a Boolean<B>>,
    ) -> Result<Self, SynthesisError> {
        let mut res = Self::one();
        let mut mul = (*self).clone();

        for bit in bits {
            let tmp = res.clone().mul(&mul);
            res = bit.select(&tmp, &res)?;
            mul.square_in_place()?;
        }
        Ok(res)
    }
}


impl<TF: PrimeField, BF: PrimeField> CondSelectGadget<BF> for Fp12Var<TF, BF>
{
    fn conditionally_select(
        cond: &Boolean<BF>,
        true_value: &Self,
        false_value: &Self,
    ) -> Result<Self, SynthesisError> {
        let c0 = Fp6Var::<TF, BF>::conditionally_select(
            cond,
            &true_value.c0,
            &false_value.c0,
        )?;
        let c1 = Fp6Var::<TF, BF>::conditionally_select(
            cond,
            &true_value.c1,
            &false_value.c1,
        )?;

        Ok(Self::new(c0, c1))
    }
}

impl<TF: PrimeField, BF: PrimeField> AbsorbGadget<BF> for Fp12Var<TF, BF>
{
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<BF>>, SynthesisError> {
        todo!()
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<BF>>, SynthesisError> {
        Ok(
            self.c0.c0.c0.to_constraint_field().unwrap().into_iter().chain(
                self.c0.c0.c1.to_constraint_field().unwrap()).chain(
                self.c0.c1.c0.to_constraint_field().unwrap()).chain(
                self.c0.c1.c1.to_constraint_field().unwrap()).chain(
                self.c0.c2.c0.to_constraint_field().unwrap()).chain(
                self.c0.c2.c1.to_constraint_field().unwrap()).chain(
                self.c1.c0.c0.to_constraint_field().unwrap()).chain(
                self.c1.c0.c1.to_constraint_field().unwrap()).chain(
                self.c1.c1.c0.to_constraint_field().unwrap()).chain(
                self.c1.c1.c1.to_constraint_field().unwrap()).chain(
                self.c1.c2.c0.to_constraint_field().unwrap()).chain(
                self.c1.c2.c1.to_constraint_field().unwrap())
                .collect()
        )
    }
}


pub fn new_fp12_variable<V: Borrow<ark_bls12_381::Fq12>, CF: PrimeField>(
    cs: impl Into<Namespace<CF>>,
    f: impl FnOnce() -> Result<V, SynthesisError>,
    mode: AllocationMode,
) -> Result<Fq12Var<CF>, SynthesisError> {
    let ns = cs.into();
    let cs = ns.cs();
    let (c0, c1) = match f() {
        Ok(fe) => (Ok(fe.borrow().c0), Ok(fe.borrow().c1)),
        Err(_) => (
            Err(SynthesisError::AssignmentMissing),
            Err(SynthesisError::AssignmentMissing),
        ),
    };

    let c0 = new_fp6_variable(ark_relations::ns!(cs, "c0"), || c0, mode)?;
    let c1 = new_fp6_variable(ark_relations::ns!(cs, "c1"), || c1, mode)?;
    Ok(Fq12Var::new(c0, c1))
}

pub fn new_fp6_variable<V: Borrow<ark_bls12_381::Fq6>, CF: PrimeField>(
    cs: impl Into<Namespace<CF>>,
    f: impl FnOnce() -> Result<V, SynthesisError>,
    mode: AllocationMode,
) -> Result<Fq6Var<CF>, SynthesisError> {
    let ns = cs.into();
    let cs = ns.cs();
    let (c0, c1, c2) = match f() {
        Ok(fe) => (Ok(fe.borrow().c0), Ok(fe.borrow().c1), Ok(fe.borrow().c2)),
        Err(_) => (
            Err(SynthesisError::AssignmentMissing),
            Err(SynthesisError::AssignmentMissing),
            Err(SynthesisError::AssignmentMissing),
        ),
    };

    let c0 = new_fp2_variable(ark_relations::ns!(cs, "c0"), || c0, mode)?;
    let c1 = new_fp2_variable(ark_relations::ns!(cs, "c1"), || c1, mode)?;
    let c2 = new_fp2_variable(ark_relations::ns!(cs, "c2"), || c2, mode)?;
    Ok(Fq6Var::new(c0, c1, c2))
}

pub fn new_fp2_variable<V: Borrow<ark_bls12_381::Fq2>, CF: PrimeField>(
    cs: impl Into<Namespace<CF>>,
    f: impl FnOnce() -> Result<V, SynthesisError>,
    mode: AllocationMode,
) -> Result<Fq2Var<CF>, SynthesisError> {
    let ns = cs.into();
    let cs = ns.cs();
    let (c0, c1) = match f() {
        Ok(fe) => (Ok(fe.borrow().c0), Ok(fe.borrow().c1)),
        Err(_) => (
            Err(SynthesisError::AssignmentMissing),
            Err(SynthesisError::AssignmentMissing),
        ),
    };

    let c0 = NonNativeFieldVar::new_variable(ark_relations::ns!(cs, "c0"), || c0, mode)?;
    let c1 = NonNativeFieldVar::new_variable(ark_relations::ns!(cs, "c1"), || c1, mode)?;
    Ok(Fq2Var::new(c0, c1))
}
