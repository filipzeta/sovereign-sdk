#![no_main]

sp1_zkvm::entrypoint!(main);

use demo_stf::MultiAddressEvmSolana;
use sha2::{Digest, Sha256};
use sov_aggregated_proof_shared::{AggregatedProofWitness, DeferredProofInput};
use sov_mock_da::MockDaSpec;
use sov_mock_zkvm::MockZkvm;
use sov_modules_api::configurable_spec::ConfigurableSpec;
use sov_modules_api::da::BlockHeaderTrait;
use sov_modules_api::execution_mode::Zk;
use sov_modules_api::AggregatedProofPublicData;
use sov_modules_api::CodeCommitment;
use sov_modules_api::DaSpec;
use sov_modules_api::Spec;
use sov_modules_api::StateTransitionPublicData;
use sov_modules_api::Storage;
use sov_rollup_interface::common::SlotNumber;
use sov_sp1_adapter::SP1;

type S = ConfigurableSpec<MockDaSpec, SP1, MockZkvm, MultiAddressEvmSolana, Zk>;

type StPubData<S, Da> =
    StateTransitionPublicData<<S as Spec>::Address, Da, <<S as Spec>::Storage as Storage>::Root>;

type AggPubData<S, Da> =
    AggregatedProofPublicData<<S as Spec>::Address, Da, <<S as Spec>::Storage as Storage>::Root>;

struct BoundaryData<Hash, Root> {
    slot_hash: Hash,
    state_root: Root,
    slot_number: SlotNumber,
}

pub fn main() {
    let witness = sp1_zkvm::io::read::<AggregatedProofWitness<MockDaSpec>>();
    let proof_inputs = witness.proof_inputs;
    let vkey_hash = witness.vkey_hash;
    let prev_outer_proof_witness = witness.prev_outer_proof_witness;

    let previous_public_data = if let Some(prev_outer_proof_witness) = prev_outer_proof_witness {
        Some(
            deserialize_and_verify_pub_data::<AggPubData<S, MockDaSpec>>(
                &prev_outer_proof_witness.public_values,
                prev_outer_proof_witness.vkey_hash,
            ),
        )
    } else {
        None
    };

    let aggregated_public_data =
        verify::<S, MockDaSpec>(proof_inputs, vkey_hash, previous_public_data.as_ref());

    sp1_zkvm::io::commit(&aggregated_public_data);
}

fn verify<S: Spec, Da: DaSpec>(
    proof_inputs: Vec<DeferredProofInput<Da>>,
    vkey_hash: [u32; 8],
    previous_agg_proof_public_data: Option<&AggPubData<S, Da>>,
) -> AggPubData<S, Da> {
    assert!(
        !proof_inputs.is_empty(),
        "Aggregated proof must contain at least one proof input"
    );

    let mut expected_prev_hash =
        previous_agg_proof_public_data.map(|public_data| public_data.final_slot_hash.clone());

    let mut expected_state_root =
        previous_agg_proof_public_data.map(|public_data| public_data.final_state_root.clone());

    let mut initial_boundary = None;
    let mut final_boundary = None;

    let mut rewarded_addresses = Vec::with_capacity(proof_inputs.len());

    for (index, proof_input) in proof_inputs.iter().enumerate() {
        let stf_public_data = deserialize_and_verify_pub_data::<StPubData<S, Da>>(
            &proof_input.public_values,
            vkey_hash,
        );

        let current_slot_number = SlotNumber::new(proof_input.da_block_header.height());

        // Check that DA blocks form a chain.
        {
            let da_block_header = &proof_input.da_block_header;
            let current_block_hash = da_block_header.hash();

            if let Some(expected_prev_hash) = &expected_prev_hash {
                assert_eq!(
                    expected_prev_hash,
                    &da_block_header.prev_hash(),
                    "DA block chain broken at index {index}: prev_hash mismatch"
                );
            }

            // Check that the slot hash from the public input matches the current block hash.
            assert_eq!(
                current_block_hash, stf_public_data.slot_hash,
                "Slot hash mismatch at index {index}: DA block header hash doesn't match public data"
            );
            expected_prev_hash = Some(current_block_hash);
        }

        // Check that state roots are sequentially related by the state transition.
        {
            if let Some(expected_state_root) = &expected_state_root {
                assert_eq!(
                    expected_state_root, &stf_public_data.initial_state_root,
                    "State root discontinuity at index {index}: previous final_state_root != current initial_state_root"
                );
            }

            expected_state_root = Some(stf_public_data.final_state_root.clone());
        }

        if initial_boundary.is_none() {
            initial_boundary = Some(BoundaryData {
                slot_hash: proof_input.da_block_header.hash(),
                state_root: stf_public_data.initial_state_root.clone(),
                slot_number: current_slot_number,
            });
        }

        rewarded_addresses.push(stf_public_data.prover_address.clone());
        final_boundary = Some(BoundaryData {
            slot_hash: proof_input.da_block_header.hash(),
            state_root: stf_public_data.final_state_root,
            slot_number: current_slot_number,
        });
    }

    let BoundaryData {
        slot_hash: initial_slot_hash,
        state_root: initial_state_root,
        slot_number: initial_slot_number,
    } = initial_boundary.expect("proof_inputs is non-empty");

    let BoundaryData {
        slot_hash: final_slot_hash,
        state_root: final_state_root,
        slot_number: final_slot_number,
    } = final_boundary.expect("proof_inputs is non-empty");

    let genesis_state_root = previous_agg_proof_public_data
        .map(|public_data| public_data.genesis_state_root.clone())
        .unwrap_or_else(|| initial_state_root.clone());

    let code_commitment = previous_agg_proof_public_data
        .map(|public_data| public_data.code_commitment.clone())
        .unwrap_or_else(CodeCommitment::default);

    AggPubData::<S, Da> {
        initial_slot_number,
        final_slot_number,
        genesis_state_root,
        initial_state_root,
        final_state_root,
        initial_slot_hash,
        final_slot_hash,
        code_commitment,
        rewarded_addresses,
    }
}

fn deserialize_and_verify_pub_data<T: serde::de::DeserializeOwned>(
    pub_values: &[u8],
    vkey_hash: [u32; 8],
) -> T {
    let public_values_digest: [u8; 32] = Sha256::digest(pub_values).into();
    sp1_zkvm::lib::verify::verify_sp1_proof(&vkey_hash, &public_values_digest);

    bincode::deserialize(pub_values)
        .unwrap_or_else(|error| panic!("Failed to deserialize aggregated public data: {error}"))
}
