use ark_bls12_377::Bls12_377;
use ark_std::test_rng;
use ark_ec::AffineCurve;
use ark_ec::twisted_edwards_extended::GroupAffine;
//use ark_bls12_381::{G1Projective as ProjectiveEngine Fq, Fr, G1Affine};
use ark_bls12_377::{G1Projective as ProjectiveEngine, Fq, Fr, Fq12};
use ark_bw6_761::BW6_761;

use ark_ff::{Field, Zero};
use ark_groth16::Groth16;
use ark_serialize::CanonicalDeserialize;

use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
use zk_tlock::{EncryptCircuit, Parameters, poseidon};
use zk_tlock::utils::from_compressed_bytes;

fn main() {
    let mut rng = test_rng();
    let bytes = [1, 2, 3];
    let msg = Fq::from_random_bytes(&bytes).unwrap();

    let params = Parameters::<ProjectiveEngine> {
        poseidon: poseidon::get_poseidon_params::<ProjectiveEngine>(2),
    };
    let gid: _ = {
        let bytes = vec![0; 576];
        from_compressed_bytes::<Fq12>(&bytes).unwrap()
    };

    let circuit = EncryptCircuit::new(
        gid.clone(),
        msg.clone().into(),
        params.clone(),
        &mut rng,
    ).unwrap();

    let (pk, _vk) = Groth16::<BW6_761>::setup(circuit, &mut rng).unwrap();

    let circuit = EncryptCircuit::new(gid, msg.clone().into(), params.clone(), &mut rng).unwrap();
    let ct = circuit.resulted_ciphertext.clone();
    let _proof = Groth16::prove(&pk, circuit, &mut rng).unwrap();

    // let public_inputs = EncryptCircuit::get_public_inputs(&ct, &params);
    // let valid_proof = Groth16::<Bls12_377>::verify(&vk, &public_inputs, &proof).unwrap();
    // assert!(valid_proof);
}
