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

type ProgramSpec = ConfigurableSpec<MockDaSpec, SP1, MockZkvm, MultiAddressEvmSolana, Zk>;

type StPubData<S, Da> =
    StateTransitionPublicData<<S as Spec>::Address, Da, <<S as Spec>::Storage as Storage>::Root>;

type AggPubData<S, Da> =
    AggregatedProofPublicData<<S as Spec>::Address, Da, <<S as Spec>::Storage as Storage>::Root>;

struct BoundaryData<Hash, Root> {
    slot_hash: Hash,
    state_root: Root,
    slot_number: SlotNumber,
}

struct VerifiedProofData<Address, Hash, Root> {
    initial_boundary: BoundaryData<Hash, Root>,
    final_boundary: BoundaryData<Hash, Root>,
    rewarded_addresses: Vec<Address>,
}

type VerifyResult<S, Da> = VerifiedProofData<
    <S as Spec>::Address,
    <Da as DaSpec>::SlotHash,
    <<S as Spec>::Storage as Storage>::Root,
>;

pub fn main() {
    let witness = sp1_zkvm::io::read::<AggregatedProofWitness<MockDaSpec>>();
    run_aggregation_program::<ProgramSpec, MockDaSpec>(witness);
}

fn run_aggregation_program<S: Spec<Da = Da>, Da: DaSpec>(witness: AggregatedProofWitness<Da>) {
    let proof_inputs = witness.proof_inputs;
    let vkey_hash = witness.vkey_hash;
    let prev_outer_proof_witness = witness.prev_outer_proof_witness;

    let previous_public_data = if let Some(prev_outer_proof_witness) = prev_outer_proof_witness {
        Some(
            deserialize_and_verify_pub_data::<AggPubData<S, Da>>(
                &prev_outer_proof_witness.public_values,
                prev_outer_proof_witness.vkey_hash,
            ),
        )
    } else {
        None
    };

    let verified_proof_data: VerifyResult<S, Da> =
        verify_proof_chain::<S, Da>(proof_inputs, vkey_hash, previous_public_data.as_ref());

    let VerifiedProofData {
        initial_boundary,
        final_boundary,
        rewarded_addresses,
    } = verified_proof_data;

    let genesis_state_root = previous_public_data
        .as_ref()
        .map(|public_data| public_data.genesis_state_root.clone())
        .unwrap_or_else(|| initial_boundary.state_root.clone());

    let code_commitment = previous_public_data
        .as_ref()
        .map(|public_data| public_data.code_commitment.clone())
        .unwrap_or_else(CodeCommitment::default);

    let aggregated_public_data = AggPubData::<S, Da> {
        initial_slot_number: initial_boundary.slot_number,
        final_slot_number: final_boundary.slot_number,
        genesis_state_root,
        initial_state_root: initial_boundary.state_root,
        final_state_root: final_boundary.state_root,
        initial_slot_hash: initial_boundary.slot_hash,
        final_slot_hash: final_boundary.slot_hash,
        code_commitment,
        rewarded_addresses,
    };

    sp1_zkvm::io::commit(&aggregated_public_data);
}

fn verify_proof_chain<S: Spec, Da: DaSpec>(
    proof_inputs: Vec<DeferredProofInput<Da>>,
    vkey_hash: [u32; 8],
    previous_agg_proof_public_data: Option<&AggPubData<S, Da>>,
) -> VerifyResult<S, Da> {
    assert!(
        !proof_inputs.is_empty(),
        "Aggregated proof must contain at least one proof input"
    );

    let mut expected_prev_slot_hash =
        previous_agg_proof_public_data.map(|public_data| public_data.final_slot_hash.clone());

    let mut expected_prev_state_root =
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

            if let Some(expected_prev_slot_hash) = &expected_prev_slot_hash {
                assert_eq!(
                    expected_prev_slot_hash,
                    &da_block_header.prev_hash(),
                    "DA block chain broken at index {index}: prev_hash mismatch"
                );
            }

            // Check that the slot hash from the public input matches the current block hash.
            assert_eq!(
                current_block_hash, stf_public_data.slot_hash,
                "Slot hash mismatch at index {index}: DA block header hash doesn't match public data"
            );
            expected_prev_slot_hash = Some(current_block_hash);
        }

        // Check that state roots are sequentially related by the state transition.
        {
            if let Some(expected_prev_state_root) = &expected_prev_state_root {
                assert_eq!(
                    expected_prev_state_root, &stf_public_data.initial_state_root,
                    "State root discontinuity at index {index}: previous final_state_root != current initial_state_root"
                );
            }

            expected_prev_state_root = Some(stf_public_data.final_state_root.clone());
        }

        if initial_boundary.is_none() {
            initial_boundary = Some(BoundaryData {
                slot_hash: proof_input.da_block_header.hash(),
                state_root: stf_public_data.initial_state_root.clone(),
                slot_number: current_slot_number.clone(),
            });
        }

        rewarded_addresses.push(stf_public_data.prover_address.clone());
        final_boundary = Some(BoundaryData {
            slot_hash: proof_input.da_block_header.hash(),
            state_root: stf_public_data.final_state_root,
            slot_number: current_slot_number,
        });
    }

    let initial_boundary = initial_boundary.expect("proof_inputs is non-empty");
    let final_boundary = final_boundary.expect("proof_inputs is non-empty");

    VerifyResult::<S, Da> {
        initial_boundary,
        final_boundary,
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
