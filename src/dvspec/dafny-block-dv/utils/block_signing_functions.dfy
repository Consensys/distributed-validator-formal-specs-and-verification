include "./block_types.dfy"
include "./block_common_functions.dfy"

module BlockSigningFunctions{
    import opened BlockTypes
    import opened BlockCommonFunctions
    
    function method {:extern} compute_signing_root<T>(
        data: T,
        domain: Domain
    ): Root
    
    function method compute_attestation_signing_root_with_attestation_and_epoch(
        attestation_data: AttestationData, 
        attestation_epoch: Epoch
    ): Root
    {
        var domain := compute_domain(DOMAIN_BEACON_ATTESTER, attestation_epoch);
        compute_signing_root(attestation_data, domain)
    }

    function method compute_randao_reveal_signing_root(slot: Slot): Root
    {   
        var epoch := compute_epoch_at_slot(slot);
        var domain := compute_domain(DOMAIN_RANDAO, epoch);
        compute_signing_root(epoch, domain)
    }
    
    function method compute_block_signing_root(block: BeaconBlock): Root
    {
        var epoch := compute_epoch_at_slot(block.slot);
        var domain := compute_domain(DOMAIN_BEACON_PROPOSER, epoch);
        compute_signing_root(block, domain)
    }   

    function method get_sign_threshold(n: nat): nat
    requires n > 0
    {
        (2 * n / 3) + 1
    }                
}