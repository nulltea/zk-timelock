use ark_std::test_rng;
use ark_bls12_381::{Bls12_381 as ProjectiveEngine, Fr, G1Affine};
use ark_ec::ProjectiveCurve;
use ark_ec::twisted_edwards_extended::{GroupAffine, GroupProjective};
use ark_ed_on_bls12_381::{
    constraints::EdwardsVar as CurveVar, EdwardsProjective as Curve, Fq, FrParameters,
};
use ark_ff::Field;
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
use zk_tlock::{EncryptCircuit, Parameters, poseidon};

type Circuit = EncryptCircuit::<Curve, CurveVar>;

fn main() {
    let mut rng = test_rng();
    let bytes = [1, 2, 3];
    let msg = Fq::from_random_bytes(&bytes).unwrap();

    let params = Parameters::<Curve> {
        poseidon: poseidon::get_poseidon_params::<Curve>(2),
    };
    let gid = {
        let bytes = hex::decode("18c158e8047c7f0436e0f572fd27828c25171d87f11b816b690fb94dd5dd0f3764044bf39735288b31e43153845fbfbb13a1119517f634aaf56423d90b436c19a1b197f7830ad94c7c141207c440ca3e603e4e3647bc65423d47bf7882ae15501991b5b211a3b2af873d9819adc48de0fd18e0946ae1764547c997cf89535a4f4605a0681517af3c3fbaeb09d27bce60000432cf64c73a6c151c58979d0887869db9c4f2e45b01dcaa503947350c9031580bfc46afd944537ea77b62d2f259210aca6eb75bdc0e4137a35534b5edd32497b09dcead32e358f358864baecf96015f9441a62bb2f382a2ed12de544bbfcf01754d4325e364675930cbdc3250bed0fdf6cb7a90d3c37c828d52f3435176a21d7dd07d3bea657ae4a66cfe17faf54119ae9a77f8006337943d5d9b96078377409e57b29e1700fe29df22ba19a340402ce45271e58b80c7f253e4e82ac99c0a007a029063de1468d6bd17d78e6c96d391c2c2a32517cbb8b97ac862ef593fd8e887ca4e73019640e3ccb69d7f2a4a1c0de4717788142389490d7638b369385a1e409e712313b7a14217fa098bea3e28730200217a9cab404bddb3db82bb5b270989ebc722be0a1e582fcb650c56f50fb61941cc3ec18901fd3a50ee431a3aca300a2a86173f0c5b59489a3267a73a4409f59222cda52b4e0fcf0b40e4979da94d699724c0959f061df747cfa2789ac896fafbe91563909e580871dc74af80750be4c1528066836b42fe6c599f9da2558c040ea7a44fb32213a37415078668cbc8c8441bf0c84cd7f51797c6bda1d37e").unwrap();
        GroupProjective::default()
    };

    let circuit = Circuit::new(
        gid.clone(),
        msg.clone().into(),
        params.clone(),
        &mut rng,
    ).unwrap();

    let (pk, vk) = Groth16::<ProjectiveEngine>::setup(circuit, &mut rng).unwrap();

    let circuit = Circuit::new(gid, msg.clone().into(), params.clone(), &mut rng).unwrap();
    let enc = circuit.resulted_ciphertext.clone();
    let proof = Groth16::prove(&pk, circuit, &mut rng).unwrap();

    let public_inputs = Circuit::get_public_inputs::<ProjectiveEngine>(&enc, &params);
    let valid_proof = Groth16::<ProjectiveEngine>::verify(&vk, &public_inputs, &proof).unwrap();
    assert!(valid_proof);
}
