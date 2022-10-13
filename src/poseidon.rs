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
    let arks = POSEIDON_ARK.iter().map(|ark| ark.iter()
                .map(|v| C::BaseField::from_str(v).map_err(|_| anyhow!("parse err")).unwrap())
                .collect::<Vec<_>>()
        ).collect::<Vec<_>>();
    let mds = POSEIDON_MDS.iter().map(|mds| mds.iter()
            .map(|v| C::BaseField::from_str(v).map_err(|_| anyhow!("parse err")).unwrap())
            .collect::<Vec<_>>()
    ).collect::<Vec<_>>();
    PoseidonConfig::new(
        POSEIDON_FULL_ROUNDS,
        POSEIDON_PARTIAL_ROUNDS,
        POSEIDON_ALPHA,
        mds,
        arks,
        POSEIDON_RATE,
        1
    )
}
