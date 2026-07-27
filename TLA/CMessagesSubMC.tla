---------------------------- MODULE CMessagesSubMC ----------------------------
EXTENDS MessageConcrete

LEMMA CMessagesSubMC == CMessages \subseteq CMC
BY DEF CMessages
=============================================================================
