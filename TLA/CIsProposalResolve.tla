-------------------------- MODULE CIsProposalResolve --------------------------
EXTENDS MessageConcrete, CFields

LEMMA CIsProposalResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE IsProposal(x) = CIsProposal(x)
<1>1. Proposals = CProposals  BY CFields
<1>2. IsProposal(x) <=> CIsProposal(x)  BY <1>1 DEF IsProposal, CProposals
<1>3. IsProposal(x) \in BOOLEAN  BY DEF IsProposal
<1>4. CIsProposal(x) \in BOOLEAN  BY DEF CIsProposal
<1> QED BY <1>2, <1>3, <1>4
=============================================================================
