include "../../../common/block_proposer/block_types.dfy"
include "../../../common/block_proposer/block_common_functions.dfy"
include "../../../common/block_proposer/block_signing_functions.dfy"

module DVC_Block_Proposer_Spec_Axioms
{
    import opened Block_Types 
    import opened Block_Common_Functions
    import opened Block_Signing_Functions

    datatype BNState = BNState(
        state_roots_of_imported_blocks: set<Root>,
        blocks_submitted: seq<SignedBeaconBlock>    
    )  

    datatype RSState = RSState(
        pubkey: BLSPubkey
    )    

    function {:axiom} bn_get_fork_version(slot: Slot): Version

    function {:axiom} bn_get_validator_index(bnState: BNState, state_id: Root, validator_id: BLSPubkey): (vi: Optional<ValidatorIndex>)
    requires state_id in bnState.state_roots_of_imported_blocks

    function {:axiom} bn_get_epoch_committees(bnState: BNState, state_id: Root, index: CommitteeIndex): (sv: seq<ValidatorIndex>) 
    requires state_id in bnState.state_roots_of_imported_blocks   

    // Don't need to use fork_version
    function {:axiom} rs_sign_block(        
        block: BeaconBlock,
        fork_version: Version,
        signing_root: Root,
        rs: RSState
    ): BLSSignature
    requires signing_root == compute_block_signing_root(block)

    lemma {:axiom} rs_block_sign_and_verification_propeties()
    ensures forall beacon_block, fork_version, signing_root, rs |
                    rs_sign_block.requires(beacon_block, fork_version, signing_root, rs) ::
                    verify_bls_signature(
                        signing_root,
                        rs_sign_block(beacon_block, fork_version, signing_root, rs),
                        rs.pubkey
                    )
    ensures forall signing_root, signature, pubkey ::
        verify_bls_signature(signing_root, signature, pubkey) <==>
            exists beacon_block, fork_version ::
            var rs := RSState(pubkey);
            && rs_sign_block.requires(beacon_block, fork_version, signing_root, rs)
            && signature == rs_sign_block(beacon_block, fork_version, signing_root, rs)

    ensures forall ad1, fv1, sr1, pk1, ad2, fv2, sr2, pk2 ::
            && rs_sign_block.requires(ad1, fv1, sr1, pk1)
            && rs_sign_block.requires(ad2, fv2, sr2, pk2)
            && rs_sign_block(ad1, fv1, sr1, pk1) == rs_sign_block(ad2, fv2, sr2, pk2) 
            ==>
            && sr1 == sr2 
            && pk1 == pk2  

    // Don't need to use fork_version
    function {:axiom} rs_sign_randao_reveal(        
        epoch: Epoch,
        fork_version: Version,
        signing_root: Root,
        rs: RSState
    ): BLSSignature
    requires signing_root == compute_randao_reveal_signing_root(epoch * SLOTS_PER_EPOCH)

}