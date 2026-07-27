------------------------ MODULE BAchievedByProposal ------------------------
EXTENDS MessageInterface, FiniteSetTheorems, MaxBSetProperty, BBallot

\* Any message's B-value is achieved by some ancestor proposal (in its own
\* Tran) whose own B-value equals it too.
LEMMA BAchievedByProposal ==
  ASSUME MessageInterfaceAssumptions, NEW w \in Messages
  PROVE \E q \in Tran(w) : IsProposal(q) /\ ProposalBal(q) = B(w) /\ B(q) = B(w)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>ne. GetProposals(w) # {}  BY <1>anp DEF AlwaysAProposal
<1>sub. GetProposals(w) \subseteq Proposals  BY DEF GetProposals
<1>fin. IsFiniteSet(GetProposals(w))
  <2>1. GetProposals(w) \subseteq Tran(w)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(w))  BY <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>choose. /\ B(w) \in {ProposalBal(z) : z \in GetProposals(w)}
           /\ \A y \in {ProposalBal(z) : z \in GetProposals(w)} : B(w) >= y
  BY <1>tok, <1>fin, <1>sub, <1>ne, MaxBSetProperty DEF B
<1> PICK q \in GetProposals(w) : B(w) = ProposalBal(q)  BY <1>choose
<1>qgp. q \in Proposals /\ q \in Tran(w)  BY DEF GetProposals
<1>qprop. IsProposal(q)  BY <1>qgp DEF IsProposal
<1>propsub. Proposals \subseteq Messages  BY <1>tok DEF TypeOKMessageInterface
<1>qmsg. q \in Messages  BY <1>qgp, <1>propsub
<1>qown. q \in GetProposals(q)
  <2>1. q \in Tran(q)  BY DEF Tran
  <2> QED BY <2>1, <1>qgp DEF GetProposals
<1>qfin. IsFiniteSet(GetProposals(q))
  <2>1. GetProposals(q) \subseteq Tran(q)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(q))  BY <1>qmsg, <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>qsub. GetProposals(q) \subseteq Proposals  BY DEF GetProposals
<1>qne. GetProposals(q) # {}  BY <1>qown
<1>choose2. /\ B(q) \in {ProposalBal(z) : z \in GetProposals(q)}
            /\ \A y \in {ProposalBal(z) : z \in GetProposals(q)} : B(q) >= y
  BY <1>tok, <1>qfin, <1>qsub, <1>qne, MaxBSetProperty DEF B
<1>bqge. B(q) >= ProposalBal(q)
  <2>pbmem. ProposalBal(q) \in {ProposalBal(z) : z \in GetProposals(q)}  BY <1>qown
  <2> QED BY <2>pbmem, <1>choose2
<1>gpsub. GetProposals(q) \subseteq GetProposals(w)
  <2>1. Tran(q) \subseteq Tran(w)  BY <1>qgp, <1>tt DEF TranTrans
  <2> QED BY <2>1 DEF GetProposals
<1>bqmem. B(q) \in {ProposalBal(z) : z \in GetProposals(w)}
  <2>1. B(q) \in {ProposalBal(z) : z \in GetProposals(q)}  BY <1>choose2
  <2> QED BY <2>1, <1>gpsub
<1>bqle. B(w) >= B(q)  BY <1>bqmem, <1>choose
<1>anp2. AlwaysAProposal  BY <1>anp
<1>bwnat. B(w) \in Ballots  BY <1>tok, <1>tf, <1>anp2, BBallot
<1>bqnat. B(q) \in Ballots  BY <1>qmsg, <1>tok, <1>tf, <1>anp2, BBallot
<1>beq. B(q) = B(w)  BY <1>bqge, <1>bqle, <1>bwnat, <1>bqnat DEF Ballots
<1> QED BY <1>qgp, <1>qprop, <1>beq
====================================================================
