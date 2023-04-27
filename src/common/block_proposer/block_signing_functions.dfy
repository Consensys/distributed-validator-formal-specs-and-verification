include "../commons.dfy"
include "./block_common_functions.dfy"

module Block_Signing_Functions{
    import opened Types
    import opened Block_Common_Functions
    
    function method {:extern} compute_signing_root<T>(
        data: T,
        domain: Domain
    ): Root

    
    
    // function method compute_attestation_signing_root_with_attestation_and_epoch(
    //     attestation_data: AttestationData, 
    //     attestation_epoch: Epoch
    // ): Root
    // {
    //     var domain := compute_domain(DOMAIN_BEACON_ATTESTER, attestation_epoch);
    //     compute_signing_root(attestation_data, domain)
    // }

    function method compute_attestation_signing_root(
        attestation_data: AttestationData, 
        fork_version: Version
    ): Root
    {
        var domain := compute_domain_with_fork_version(DOMAIN_BEACON_ATTESTER, fork_version);
        compute_signing_root(attestation_data, domain)
    }

    function method compute_randao_reveal_signing_root(slot: Slot): Root
    {   
        var epoch := compute_epoch_at_slot(slot);
        var domain := compute_domain_with_epoch(DOMAIN_RANDAO, epoch);
        compute_signing_root(epoch, domain)
    }
    
    function method compute_block_signing_root(block: BeaconBlock): Root
    {
        var epoch := compute_epoch_at_slot(block.slot);
        var domain := compute_domain_with_epoch(DOMAIN_BEACON_PROPOSER, epoch);
        compute_signing_root(block, domain)
    }   

    function method get_sign_threshold(n: nat): nat
    requires n > 0
    {
        (2 * n / 3) + 1
    }   

    predicate method {:extern} verify_bls_signature<T>(
        data: T,
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

    lemma {:axiom} compute_signing_root_properties<T>()
    ensures forall da1, do1, da2, do2 ::
        compute_signing_root<T>(da1, do1) == compute_signing_root<T>(da2, do2) ==>
            && da1 == da2 
            && do1 == do2

}