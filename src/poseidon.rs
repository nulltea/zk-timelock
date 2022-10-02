use crate::parameters::*;
use ark_ec::ProjectiveCurve;
use ark_ff::PrimeField;
use ark_sponge::poseidon::PoseidonParameters;
use ark_sponge::Absorb;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::str::FromStr;

// returns optimized for constraints
pub fn get_poseidon_params<C: ProjectiveCurve>(_rate: usize) -> PoseidonParameters<C::BaseField>
where
    C::BaseField: PrimeField,
    <C::BaseField as FromStr>::Err: Debug,
{
    let arks = P1["ark"]
        .members()
        .map(|ark| {
            ark.members()
                .map(|v| C::BaseField::from_str(v.as_str().unwrap()).unwrap())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mds = P1["mds"]
        .members()
        .map(|m| {
            m.members()
                .map(|v| C::BaseField::from_str(v.as_str().unwrap()).unwrap())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    PoseidonParameters::new(
        P1["full_rounds"].as_u32().unwrap(),
        P1["partial_rounds"].as_u32().unwrap(),
        P1["alpha"].as_u64().unwrap(),
        mds,
        arks,
    )
}
