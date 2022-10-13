use std::ops::MulAssign;
use ark_bls12_377::Bls12_377;
use ark_bls12_381::Bls12_381;
use ark_bw6_761::BW6_761;
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::Field;
use ark_groth16::Groth16;
use ark_snark::{CircuitSpecificSetupSNARK, SNARK};
use ark_std::{rand, test_rng, UniformRand};
use sha2::Digest;
use tracing::{info_span, info, Level};
use tracing_subscriber::fmt::{format, init};
use tracing_subscriber::fmt::format::FmtSpan;
use zk_tlock::{Circuit, GeminiNativeCircuit, NonnativeCircuit, Parameters};
use zk_tlock::utils::ZkCryptoDeserialize;
use ark_std::rand::Rng;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;

fn test_groth16_native_bls12_377() {
    type TestCircuit = Circuit::<Bls12_377, ark_bls12_377::Parameters>;
    let mut rng = rand::thread_rng();
    let bytes = [1, 2, 3];
    let msg = ark_bls12_377::Fq::from_random_bytes(&bytes).unwrap();

    let (master, priv_key) = {
        let sk = ark_bls12_377::Fr::rand(&mut rng);
        let mut master = {
            let mut g = ark_bls12_377::G1Projective::generator();
            g.mul_assign(&sk);
            g
        };
        let msg_hash = ark_bls12_377::G2Projective::generator();
        let signature = {
            let mut h = msg_hash;
            h.mul_assign(sk);
            h
        };
        (master.into_affine(), signature.into_affine())
    };

    let round_number = 1000u64;
    let id = {
        let mut hash = sha2::Sha256::new();
        hash.update(&round_number.to_be_bytes());
        &hash.finalize().to_vec()[0..32]
    };

    let circuit = info_span!("encrypt-message").in_scope(|| {
        Circuit::<ark_bls12_377::Bls12_377, ark_bls12_377::Parameters>::new(
            master.clone(),
            &id,
            msg.clone().into(),
            &mut rng)
    }).unwrap();

    let (pk, vk) = info_span!("groth16::setup").in_scope(||
        Groth16::<BW6_761>::setup(circuit, &mut rng)
    ).unwrap();

    let circuit = TestCircuit::new(master, id, msg.clone().into(), &mut rng).unwrap();
    let ct = circuit.ciphertext.clone();

    let public_input = TestCircuit::get_public_inputs(&circuit.gid, &ct);

    let proof = info_span!("groth16::prove").in_scope(||
        Groth16::prove(&pk, circuit, &mut rng)
    ).unwrap();

    let verified = info_span!("groth16::verify").in_scope(||
        Groth16::verify(&vk, &public_input, &proof)
    ).unwrap();

    assert!(verified);

    let pt = info_span!("decrypt-message").in_scope(||
        TestCircuit::decrypt(&priv_key, &ct)
    ).unwrap();

    assert_eq!(msg, pt)
}

fn test_groth16_nonnative_bls12_381() {
    type TestCircuit = NonnativeCircuit::<ark_bls12_377::G1Projective>;

    let mut rng = rand::thread_rng();
    let bytes = [1, 2, 3];
    let msg = ark_bls12_381::Fq::from_random_bytes(&bytes).unwrap();

    let master: _ = {
        let bytes = hex::decode("8200fc249deb0148eb918d6e213980c5d01acd7fc251900d9260136da3b54836ce125172399ddc69c4e3e11429b62c11").unwrap();
        ark_bls12_381::G1Affine::deserialize_zk_crypto(&bytes).unwrap()
    };
    let round_number = 1000u64;
    let id = {
        let mut hash = sha2::Sha256::new();
        hash.update(&round_number.to_be_bytes());
        &hash.finalize().to_vec()[0..32]
    };

    let circuit = info_span!("encrypt-message").in_scope(|| {
        TestCircuit::new(
            master.clone(),
            &id,
            msg.clone().into(),
            &mut rng)
    }).unwrap();

    let (pk, _vk) = info_span!("groth16::setup").in_scope(||
        Groth16::<BW6_761>::setup(circuit, &mut rng)
    ).unwrap();

    let circuit = TestCircuit::new(master, id, msg.clone().into(), &mut rng).unwrap();
    let ct = circuit.ciphertext.clone();
    // let public_input = TestCircuit::get_public_inputs(&circuit.gid, &ct);

    let _proof = info_span!("groth16::prove").in_scope(||
        Groth16::prove(&pk, circuit, &mut rng)
    ).unwrap();

    let priv_key = {
        let bytes = hex::decode("a4721e6c3eafcd823f138cd29c6c82e8c5149101d0bb4bafddbac1c2d1fe3738895e4e21dd4b8b41bf007046440220910bb1cdb91f50a84a0d7f33ff2e8577aa62ac64b35a291a728a9db5ac91e06d1312b48a376138d77b4d6ad27c24221afe").unwrap();
        ark_bls12_381::G2Affine::deserialize_zk_crypto(&bytes).unwrap()
    };

    // let verified = info_span!("groth16::verify").in_scope(||
    //     Groth16::verify(&vk, &public_input, &proof)
    // ).unwrap();

    // assert!(verified);

    let pt = info_span!("decrypt-message").in_scope(||
        TestCircuit::decrypt(&priv_key, &ct)
    ).unwrap();

    assert_eq!(msg, pt)
}

fn test_gemini_native_yata_127() {
    type TestCircuit = Circuit::<Bls12_381, ark_bls12_381::Parameters>;

    let mut rng = rand::thread_rng();
    let bytes = [1, 2, 3];
    let msg = ark_bls12_381::Fq::from_random_bytes(&bytes).unwrap();

    let master: _ = {
        let bytes = hex::decode("8200fc249deb0148eb918d6e213980c5d01acd7fc251900d9260136da3b54836ce125172399ddc69c4e3e11429b62c11").unwrap();
        ark_bls12_381::G1Affine::deserialize_zk_crypto(&bytes).unwrap()
    };
    let round_number = 1000u64;
    let id = {
        let mut hash = sha2::Sha256::new();
        hash.update(&round_number.to_be_bytes());
        &hash.finalize().to_vec()[0..32]
    };

    let circuit = info_span!("encrypt-message").in_scope(|| {
        GeminiNativeCircuit(TestCircuit::new(
            master.clone(),
            &id,
            msg.clone().into(),
            &mut rng).unwrap())
    });

    let ct = circuit.0.ciphertext.clone();

    let r1cs = info_span!("gemini::generate_relation").in_scope(||
        ark_gemini::circuit::generate_relation::<ark_bls12_381::Fq, GeminiNativeCircuit>(circuit)
    );

    info!("r1cs size: {}", r1cs.a.len());

    let num_constraints = 68000;
    let num_variables = 100;
    let num_non_zero = 68000;

    let ck = info_span!("gemini::setup").in_scope(||
        ark_gemini::kzg::CommitterKey::<zk_tlock::yt6_776::YT6_776>::new(
        num_non_zero + num_variables + num_constraints,
        5,
        &mut rng,
    ));

    let _proof = info_span!("gemini::prove").in_scope(||
        ark_gemini::psnark::Proof::new_time(&r1cs, &ck)
    );

    let priv_key = {
        let bytes = hex::decode("a4721e6c3eafcd823f138cd29c6c82e8c5149101d0bb4bafddbac1c2d1fe3738895e4e21dd4b8b41bf007046440220910bb1cdb91f50a84a0d7f33ff2e8577aa62ac64b35a291a728a9db5ac91e06d1312b48a376138d77b4d6ad27c24221afe").unwrap();
        ark_bls12_381::G2Affine::deserialize_zk_crypto(&bytes).unwrap()
    };

    let pt = info_span!("decrypt-message").in_scope(||
        TestCircuit::decrypt(&priv_key, &ct)
    ).unwrap();

    assert_eq!(msg, pt)
}

fn setup_tracing() {
    let filter = tracing_subscriber::filter::Targets::new()
        .with_target("ibe_benchmark", Level::INFO);

    let fmt = tracing_subscriber::fmt::layer()
        .with_span_events(FmtSpan::CLOSE);

    let _ = tracing_subscriber::registry()
        .with(fmt)
        .with(filter)
        .init();
}

fn main() {
    setup_tracing();

    println!("Groth16 (native) on BLS12-377");
    test_groth16_native_bls12_377();

    println!("Groth16 (nonnative) on BLS12-381");
    test_groth16_nonnative_bls12_381();

    println!("Gemini (native) on Yata-127");
    test_gemini_native_yata_127();
}
