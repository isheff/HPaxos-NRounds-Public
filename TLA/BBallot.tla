----------------------------- MODULE BBallot -----------------------------
\*   FiniteSetTheorems -> FS_Subset
\*   MaxBSetProperty   -> cited lemma
EXTENDS MessageInterface, FiniteSetTheorems, MaxBSetProperty

\* B(m) is always a valid ballot. Needs AlwaysAProposal to guarantee
\* GetProposals(m) # {}, so Max({ProposalBal(x) : x \in GetProposals(m)}) is
\* well-defined.
LEMMA BBallot ==
  ASSUME AlwaysAProposal, TranFinite, TypeOKMessageInterface, NEW m \in Messages
  PROVE B(m) \in Ballots
<1>ne. GetProposals(m) # {}  BY DEF AlwaysAProposal
<1>fin. IsFiniteSet(GetProposals(m))
  <2>1. GetProposals(m) \subseteq Tran(m)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(m))  BY DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>sub. GetProposals(m) \subseteq Proposals  BY DEF GetProposals
<1>typeOK. TypeOKMessageInterface  OBVIOUS
<1>mbp. /\ Max({ProposalBal(x) : x \in GetProposals(m)}) \in {ProposalBal(x) : x \in GetProposals(m)}
        /\ \A y \in {ProposalBal(x) : x \in GetProposals(m)} :
             Max({ProposalBal(x) : x \in GetProposals(m)}) >= y
  BY <1>fin, <1>ne, <1>sub, <1>typeOK, MaxBSetProperty
<1>1. B(m) \in {ProposalBal(x) : x \in GetProposals(m)}  BY <1>mbp DEF B
<1>2. \A x \in GetProposals(m) : ProposalBal(x) \in Ballots
  <2>1. ASSUME NEW x \in GetProposals(m) PROVE ProposalBal(x) \in Ballots
    <3>1. x \in Proposals  BY <2>1 DEF GetProposals
    <3>2. MessageInterface.proposalbal \in [Proposals -> Ballots]
      BY DEF TypeOKMessageInterface
    <3> QED BY <3>1, <3>2 DEF ProposalBal
  <2> QED BY <2>1
<1>3. PICK x \in GetProposals(m) : B(m) = ProposalBal(x)  BY <1>1
<1> QED BY <1>3, <1>2
====================================================================
