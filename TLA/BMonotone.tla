----------------------------- MODULE BMonotone -----------------------------
EXTENDS MessageInterface, FiniteSetTheorems, MaxBSetProperty, TranSubMessages

\* Ballots never increase along Tran: an ancestor's proposals are among the
\* descendant's proposals.
LEMMA BMonotone ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         NEW x \in Messages, NEW y \in Tran(x)
  PROVE B(y) <= B(x)
<1>finX. IsFiniteSet(GetProposals(x))
  <2>1. GetProposals(x) \subseteq Tran(x)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(x))  BY DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>subX. GetProposals(x) \subseteq Proposals  BY DEF GetProposals
<1>neX. GetProposals(x) # {}  BY DEF AlwaysAProposal
<1>Xchoose. /\ B(x) \in {ProposalBal(z) : z \in GetProposals(x)}
            /\ \A w \in {ProposalBal(z) : z \in GetProposals(x)} : B(x) >= w
  BY <1>finX, <1>subX, <1>neX, MaxBSetProperty DEF B
<1>yM. y \in Messages  BY TranSubMessages
<1>subT. Tran(y) \subseteq Tran(x)  BY DEF TranTrans
<1>subGP. GetProposals(y) \subseteq GetProposals(x)  BY <1>subT DEF GetProposals
<1>finY. IsFiniteSet(GetProposals(y))
  <2>1. GetProposals(y) \subseteq Tran(y)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(y))  BY <1>yM DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>subY. GetProposals(y) \subseteq Proposals  BY DEF GetProposals
<1>neY. GetProposals(y) # {}  BY <1>yM DEF AlwaysAProposal
<1>Ychoose. /\ B(y) \in {ProposalBal(z) : z \in GetProposals(y)}
            /\ \A w \in {ProposalBal(z) : z \in GetProposals(y)} : B(y) >= w
  BY <1>finY, <1>subY, <1>neY, MaxBSetProperty DEF B
<1>1. B(y) \in {ProposalBal(z) : z \in GetProposals(x)}
  <2>1. PICK zz \in GetProposals(y) : B(y) = ProposalBal(zz)  BY <1>Ychoose
  <2>2. zz \in GetProposals(x)  BY <2>1, <1>subGP
  <2> QED BY <2>1, <2>2
<1> QED BY <1>1, <1>Xchoose
====================================================================
