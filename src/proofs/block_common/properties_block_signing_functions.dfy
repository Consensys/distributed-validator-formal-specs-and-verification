include "../../common/commons.dfy"
include "../../common/block_proposer/block_common_functions.dfy"
include "../../common/block_proposer/block_signing_functions.dfy"
include "./properties_block_common_functions.dfy"

import opened Types
import opened Block_Common_Functions
import opened Block_Signing_Functions 


lemma {:axiom} compute_signing_root_properties<T>(da1: T, do1: Domain, da2: T, do2: Domain)
requires compute_signing_root(da1, do1) == compute_signing_root(da2, do2)
ensures da1 == da2 && do1 == do2                

lemma compute_attestation_signing_root_with_attestation_and_epoch_properties(
         da1: AttestationData, ep1: Epoch, 
         da2: AttestationData, ep2: Epoch)
requires compute_attestation_signing_root_with_attestation_and_epoch(da1, ep1) ==  
         compute_attestation_signing_root_with_attestation_and_epoch(da2, ep2) 
ensures da1 == da2 && ep1 == ep2 
{
   var dom1 := compute_domain(DOMAIN_BEACON_ATTESTER, ep1);
   var dom2 := compute_domain(DOMAIN_BEACON_ATTESTER, ep2);
   compute_signing_root_properties<AttestationData>(da1, dom1, da2, dom2);
   compute_domain_properties(DOMAIN_BEACON_ATTESTER, ep1, DOMAIN_BEACON_ATTESTER, ep2);
}
 
lemma compute_randao_reveal_signing_root_properties(slot1: Slot, slot2: Slot)
requires compute_randao_reveal_signing_root(slot1) == compute_randao_reveal_signing_root(slot2) 
ensures compute_epoch_at_slot(slot1) == compute_epoch_at_slot(slot2)
{  
   var ep1: Epoch :| compute_epoch_at_slot(slot1) == ep1;
   var ep2: Epoch :| compute_epoch_at_slot(slot2) == ep2;
   var dom1: Domain :| dom1 == compute_domain(DOMAIN_RANDAO, ep1);
   var dom2: Domain :| dom2 == compute_domain(DOMAIN_RANDAO, ep2);   
   compute_signing_root_properties<Epoch>(ep1, dom1, ep2, dom2);   
}

lemma compute_block_signing_root_properties(b1: BeaconBlock, b2: BeaconBlock)
requires compute_block_signing_root(b1) == compute_block_signing_root(b2) 
ensures b1 == b2 
{
   var ep1 := compute_epoch_at_slot(b1.slot);
   var ep2 := compute_epoch_at_slot(b2.slot);
   var dom1 := compute_domain(DOMAIN_BEACON_PROPOSER, ep1);
   var dom2 := compute_domain(DOMAIN_BEACON_PROPOSER, ep2);
   compute_signing_root_properties<BeaconBlock>(b1, dom1, b2, dom2);
}

        