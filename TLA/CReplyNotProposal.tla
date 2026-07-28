--------------------------- MODULE CReplyNotProposal ---------------------------
\* The reply payload is not a proposal payload.  CProposal's records carry a
\* ballot field and type "proposal"; this one does not.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CReplyNotProposal == [type |-> "reply"] \notin CProposal
BY DEF CProposal
=============================================================================
