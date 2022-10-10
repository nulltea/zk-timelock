use crate::parameters::*;
use ark_ec::CurveGroup;
use ark_ff::PrimeField;
use ark_sponge::poseidon::PoseidonConfig;
use ark_sponge::Absorb;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::str::FromStr;
use anyhow::anyhow;

// returns optimized for constraints
pub fn get_poseidon_params<C: CurveGroup>(_rate: usize) -> PoseidonConfig<C::BaseField>
where
    C::BaseField: PrimeField,
{
    let arks = P1["ark"]
        .members()
        .map(|ark| {
            ark.members()
                .map(|v| C::BaseField::from_str(v.as_str().unwrap()).map_err(|_| anyhow!("parse err")).unwrap())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mds = P1["mds"]
        .members()
        .map(|m| {
            m.members()
                .map(|v| C::BaseField::from_str(v.as_str().unwrap()).map_err(|_| anyhow!("parse err")).unwrap())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    PoseidonConfig::new(
        P1["full_rounds"].as_usize().unwrap(),
        P1["partial_rounds"].as_usize().unwrap(),
        P1["alpha"].as_u64().unwrap(),
        mds,
        arks,
        2,
        1
    )
}
