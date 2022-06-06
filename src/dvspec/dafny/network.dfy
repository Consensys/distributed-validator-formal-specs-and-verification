include "commons.dfy"

module NetworkM
{
    import opened Types
    // import opened L1_SpecTypes

    datatype Network<M> = Network(
        messagesSentToNodeYetToBeReceived: map<BLSPubkey, multiset<M>>,
        allMessagesSent: set<M>
    )


    predicate NetworkInit<M>(
        e: Network<M>,
        all_nodes: set<BLSPubkey>
    )
    {
        && e.messagesSentToNodeYetToBeReceived.Keys == all_nodes
        && forall v | v in e.messagesSentToNodeYetToBeReceived.Values :: v == multiset{}
    }

    predicate NetworkDeliverNext<M>(
        e: Network<M>,
        e': Network<M>,
        n: BLSPubkey,
        messagesToBeBroadcast: set<M>,
        messagesReceived: set<M>
    )
    {
        && e'.messagesSentToNodeYetToBeReceived.Keys == e.messagesSentToNodeYetToBeReceived.Keys
        && n in e.messagesSentToNodeYetToBeReceived.Keys
        && multiset(messagesReceived) <= e.messagesSentToNodeYetToBeReceived[n]
        && |messagesReceived| <= 1
        && e'.messagesSentToNodeYetToBeReceived == e.messagesSentToNodeYetToBeReceived[
            n := e.messagesSentToNodeYetToBeReceived[n] - multiset(messagesReceived) + multiset(messagesToBeBroadcast)
        ]
        && e'.allMessagesSent == e.allMessagesSent + messagesToBeBroadcast
    }

    // predicate NetworkStutter(
    //     e: Network,
    //     e': Network
    // )
    // {
    //     e' == e
    // }

    predicate NetworkNext<M>(
        e: Network,
        e': Network,
        n : Optional<BLSPubkey>,
        messagesSentByTheNodes: set<M>,
        messagesReceivedByTheNodes: set<M>
    )
    {
        || (
            && n.isPresent()
            && NetworkDeliverNext(e, e', n.safe_get(), messagesSentByTheNodes,messagesReceivedByTheNodes)
        )
        // || (
        //     && !n.isPresent()
        //     && NetworkStutter(e, e')
        //     && messagesSentByTheNodes == {}
        //     && messagesReceivedByTheNodes == {}
        // )
    }
}