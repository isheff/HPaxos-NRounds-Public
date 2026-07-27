-------------------------- MODULE CProposalBalResolve --------------------------
EXTENDS MessageConcrete

LEMMA CProposalBalResolve == ASSUME MessageInterface = CMI, NEW p \in CProposals
  PROVE ProposalBal(p) = p.payload.ballot
<1>1. ProposalBal(p) = MessageInterface.proposalbal[p]  BY DEF ProposalBal
<1>2. MessageInterface.proposalbal[p] = p.payload.ballot  BY DEF CMI, CProposalBalField
<1> QED BY <1>1, <1>2
=============================================================================
