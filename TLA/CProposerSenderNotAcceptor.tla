---------------------- MODULE CProposerSenderNotAcceptor ----------------------
EXTENDS MessageConcrete, CExistsOutsideAcceptors

LEMMA CProposerSenderNotAcceptor == CProposerSender \notin Acceptors
BY CExistsOutsideAcceptors DEF CProposerSender
=============================================================================
