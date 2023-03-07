include "../../common/block_proposer/block_common_functions.dfy"
include "../../common/block_proposer/block_types.dfy"

// This module currently specifies an asynchronous network
module Block_Network_Spec
{
    import opened Block_Types
    import opened Block_Common_Functions
    datatype Network<M> = Network(
        messagesInTransit: multiset<MessaageWithRecipient>,
        allMessagesSent: set<M>
    )


    predicate Init<M>(
        e: Network<M>,
        all_nodes: set<BLSPubkey>
    )
    {
        && e.messagesInTransit == multiset{}
        && e.allMessagesSent == {}
    }

    predicate Next<M>(
        e: Network<M>,
        e': Network<M>,
        n: BLSPubkey,
        messagesToBeSent: set<MessaageWithRecipient<M>>,
        messagesReceived: set<M>
    )
    {
        && var messagesReceivedWithRecipient := multiset(addReceipientToMessages(messagesReceived, n));
        && |messagesReceived| <= 1
        && messagesReceivedWithRecipient <= e.messagesInTransit
        && e'.messagesInTransit == e.messagesInTransit - messagesReceivedWithRecipient + multiset(messagesToBeSent)
        && e'.allMessagesSent == e.allMessagesSent + getMessagesFromMessagesWithRecipient(messagesToBeSent)
    }
}