use crate::yata_127::*;
use ark_algebra_test_templates::*;

test_group!(g1; G1Projective; sw);
test_group!(g2; G2Projective; sw);
test_group!(pairing_output; ark_ec::pairing::PairingOutput<Yata>; msm);
test_pairing!(pairing; crate::yata_127::Yata);
