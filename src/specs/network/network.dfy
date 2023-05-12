include "../../common/commons.dfy"

// This module currently specifies an asynchronous network.
// Currently, there are three separated networks for attestation shares, randao shares, and block shares.
module NetworkSpec
{
    import opened Types
    import opened Common_Functions

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