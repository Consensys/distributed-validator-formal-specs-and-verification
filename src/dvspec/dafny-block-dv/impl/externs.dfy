include "../utils/types.dfy"
include "../utils/common-functions.dfy"
include "../utils/signing-functions.dfy"

module DVC_Externs
{
    import opened Types
    import opened CommonFunctions
    import opened SigningFunctions

    class Consensus 
    {
        ghost var sent_consensus_commands: seq<ConsensusCommand>

        constructor()
        {
            sent_consensus_commands := [];
        }

        method {:extern} start(
            id: Slot
        )
        ensures sent_consensus_commands == old(sent_consensus_commands) + [ConsensusCommand.StartConsensusOnBlock(id)]

        method {:extern} stop(
            id: Slot
        )
        ensures sent_consensus_commands == old(sent_consensus_commands) + [ConsensusCommand.StopConsensusOnBlock(id)]        

    }     

    class Network  
    {
        ghost var sent_block_share: seq<set<MessaageWithRecipient<SignedBeaconBlock>>>;
        ghost var sent_randao_share: seq<set<MessaageWithRecipient<RandaoShare>>>;


        constructor()
        {
            sent_block_share := [];
            sent_randao_share := [];
        }

        method {:extern} send_block_share(block_share: SignedBeaconBlock, receipients: set<BLSPubkey>)
        ensures sent_block_share == old(sent_block_share)  + [wrapMessageWithRecipients(block_share, receipients)]  

        method {:extern} send_randao_share(randao_share: RandaoShare, receipients: set<BLSPubkey>)
        ensures sent_randao_share == old(sent_randao_share)  + [wrapMessageWithRecipients(randao_share, receipients)]
    }

    class BeaconNode
    {        
        ghost const submitted_signed_block: seq<SignedBeaconBlock>; 

        constructor()
        {
            submitted_signed_block := [];     
        }

        method {:extern} get_fork_version(s: Slot) returns (v: Version)

        method {:extern} submit_signed_block(block: SignedBeaconBlock)
        ensures submitted_signed_block == old(submitted_signed_block) + [block]

 
    }

    class RemoteSigner
    {
        const pubkey: BLSPubkey;
        const M: int;

        constructor(
            pubkey: BLSPubkey,
            M: int
        )
        {
            this.pubkey := pubkey;
            this.M := M;
        }

        // eth_node_interface.py --> rs_sign_block
        method {:extern} sign_block(
            block: BeaconBlock,
            fork_version: Version, 
            signing_root: Root           
        ) returns (s: BLSSignature)
        requires signing_root == compute_block_signing_root(block)

        // eth_node_interface.py --> rs_sign_randao_reveal
        // Check the pre-condition that is based on the first slot of an epoch.
        method {:extern} sign_randao_reveal(
            epoch: Epoch,
            fork_version: Version, 
            signing_root: Root           
        ) returns (s: BLSSignature)
        requires signing_root == compute_randao_reveal_signing_root(epoch * SLOTS_PER_EPOCH)
    }
}

