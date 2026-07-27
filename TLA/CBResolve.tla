------------------------------- MODULE CBResolve -------------------------------
EXTENDS MessageConcrete, CFields, CTranResolve, CMessageTranClosed,
        CProposalBalResolve

\* B(x) resolves to CB(x) for any already-Message x, given MessageInterface=CMI.
LEMMA CBResolve == ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE B(x) = CB(x)
<1>1. B(x) = Max({ProposalBal(y) : y \in GetProposals(x)})  BY DEF B
<1>2. GetProposals(x) = Proposals \cap Tran(x)  BY DEF GetProposals
<1>3. Proposals = CProposals  BY CFields
<1>4. Tran(x) = CTran(x)  BY CTranResolve
<1>5. GetProposals(x) = CProposals \cap CTran(x)  BY <1>2, <1>3, <1>4
<1>6. CTran(x) \subseteq CMessages  BY CMessageTranClosed
<1>7. CProposals \cap CTran(x) = {y \in CTran(x) : CIsProposal(y)}
  <2> SUFFICES ASSUME NEW y \in CTran(x)
               PROVE y \in CProposals <=> CIsProposal(y)
    OBVIOUS
  <2>1. y \in CMessages  BY <1>6
  <2> QED BY <2>1 DEF CProposals
<1>8. GetProposals(x) = {y \in CTran(x) : CIsProposal(y)}  BY <1>5, <1>7
<1>9. \A y \in GetProposals(x) : ProposalBal(y) = y.payload.ballot
  <2> SUFFICES ASSUME NEW y \in GetProposals(x) PROVE ProposalBal(y) = y.payload.ballot
    OBVIOUS
  <2>1. y \in CProposals  BY <1>5
  <2> QED BY <2>1, CProposalBalResolve
<1>10. {ProposalBal(y) : y \in GetProposals(x)} = {y.payload.ballot : y \in {y \in CTran(x) : CIsProposal(y)}}
  BY <1>8, <1>9
<1> QED BY <1>1, <1>10 DEF CB
=============================================================================
