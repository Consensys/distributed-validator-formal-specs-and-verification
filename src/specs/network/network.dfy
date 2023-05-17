include "../../common/commons.dfy"

// This module currently specifies an asynchronous network.
// Currently, there are three separated networks for attestation shares, randao shares, and block shares.
module Network_Spec
{
    import opened Types
    import opened Common_Functions

    predicate init<M>(
        e: Network<M>,
        all_nodes: set<BLSPubkey>
    )
    {
        && e.messagesInTransit == multiset{}
        && e.allMessagesSent == {}
    }

    predicate next<M>(
        e: Network<M>,
        e': Network<M>,
        n: BLSPubkey,
        messagesToBeSent: set<MessaageWithRecipient<M>>,
        messagesReceived: set<M>
    )
    {
        && var messagesReceivedWithRecipient := multiset(f_get_quorum_card(messagesReceived, n));
        && |messagesReceived| <= 1
        && messagesReceivedWithRecipient <= e.messagesInTransit
        && e'.messagesInTransit == e.messagesInTransit - messagesReceivedWithRecipient + multiset(messagesToBeSent)
        && e'.allMessagesSent == e.allMessagesSent + f_get_messages_from_messages_with_recipients(messagesToBeSent)
    }
}