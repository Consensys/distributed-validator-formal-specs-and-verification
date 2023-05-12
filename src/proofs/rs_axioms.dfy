include "../common/commons.dfy"

module RS_Axioms
{
    import opened Types 
    import opened Signing_Methods

    function {:axiom} rs_sign_attestation(
        attestation_data: AttestationData, 
        fork_version: Version, 
        signing_root: Root,
        rs: RSState
    ): BLSSignature
    requires signing_root == compute_attestation_signing_root(attestation_data, fork_version)

    lemma {:axiom} rs_attestation_sign_and_verification_propeties()
    ensures forall attestation_data, fork_version, signing_root, rs |
                    rs_sign_attestation.requires(attestation_data, fork_version, signing_root, rs) ::
                    verify_bls_signature(
                        signing_root,
                        rs_sign_attestation(attestation_data, fork_version, signing_root, rs),
                        rs.pubkey
                    )
    ensures forall signing_root, signature, pubkey ::
        verify_bls_signature(signing_root, signature, pubkey) <==>
            exists attestation_data, fork_version ::
            var rs := RSState(pubkey);
            && rs_sign_attestation.requires(attestation_data, fork_version, signing_root, rs)
            && signature == rs_sign_attestation(attestation_data, fork_version, signing_root, rs)

    ensures forall ad1, fv1, sr1, pk1, ad2, fv2, sr2, pk2 ::
            && rs_sign_attestation.requires(ad1, fv1, sr1, pk1)
            && rs_sign_attestation.requires(ad2, fv2, sr2, pk2)
            && rs_sign_attestation(ad1, fv1, sr1, pk1) == rs_sign_attestation(ad2, fv2, sr2, pk2) 
            ==>
            && sr1 == sr2 
            && pk1 == pk2         


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

    lemma {:axiom} compute_signing_root_properties<T>()
    ensures forall da1, do1, da2, do2 ::
        compute_signing_root<T>(da1, do1) == compute_signing_root<T>(da2, do2) ==>
            && da1 == da2 
            && do1 == do2

    predicate {:extern} verify_bls_signature(
        data: Root,
        signature: BLSSignature,
        pubkey: BLSPubkey
    )   

    lemma {:axiom} lem_verify_bls_signature()
    ensures 
        forall d: Root, s, pk1, pk2 |
            && verify_bls_signature(d, s, pk1)
            && verify_bls_signature(d, s, pk2)
            ::
            pk1 == pk2
    ensures 
        forall d: Root, s1, s2, pk |
            && verify_bls_signature(d, s1, pk)
            && verify_bls_signature(d, s2, pk)
            ::
            s1 == s2            
    ensures 
        forall d1: Root, d2: Root, s, pk |
            && verify_bls_signature(d1, s, pk)
            && verify_bls_signature(d2, s, pk)
            ::
            d1 == d2           
}