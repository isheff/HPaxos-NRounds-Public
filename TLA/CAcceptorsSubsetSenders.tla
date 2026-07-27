------------------------ MODULE CAcceptorsSubsetSenders ------------------------
EXTENDS MessageConcrete, CFields

LEMMA CAcceptorsSubsetSenders == ASSUME MessageInterface = CMI PROVE AcceptorsSubsetSenders
<1>1. Senders = CSenders  BY CFields
<1>2. Acceptors \subseteq CSenders  BY DEF CSenders
<1> QED BY <1>1, <1>2 DEF AcceptorsSubsetSenders
=============================================================================
