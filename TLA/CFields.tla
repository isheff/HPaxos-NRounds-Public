-------------------------------- MODULE CFields --------------------------------
EXTENDS MessageConcrete

LEMMA CFields == ASSUME MessageInterface = CMI
  PROVE /\ Messages = CMessages
        /\ Proposals = CProposals
        /\ Senders = CSenders
  BY DEF Messages, Proposals, Senders, CMI
=============================================================================
