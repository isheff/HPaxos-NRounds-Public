--------------------------- MODULE ProposalBalOfP ---------------------------
EXTENDS MessageInterface, FiniteSetTheorems,
        MaxBSetProperty, ProposalBalLeB, BBallot

LEMMA ProposalBalOfP ==
  ASSUME MessageInterfaceAssumptions, NEW mm \in SUBSET Messages, NEW p, NEW b \in Ballots,
         p \in Proposals, TranExclusive(p) = TranClosure(mm), B(p) = b,
         \A x \in TranClosure(mm) : B(x) < b
  PROVE ProposalBal(p) = b
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>propsub. Proposals \subseteq Messages  BY <1>tok DEF TypeOKMessageInterface
<1>pm. p \in Messages  BY <1>propsub
<1>pgp. p \in GetProposals(p)
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1 DEF GetProposals
<1>fin. IsFiniteSet(GetProposals(p))
  <2>1. GetProposals(p) \subseteq Tran(p)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(p))  BY <1>pm, <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>ne. GetProposals(p) # {}  BY <1>pgp
<1>sub. GetProposals(p) \subseteq Proposals  BY DEF GetProposals
<1>choose. /\ B(p) \in {ProposalBal(z) : z \in GetProposals(p)}
           /\ \A w \in {ProposalBal(z) : z \in GetProposals(p)} : B(p) >= w
  BY <1>tok, <1>fin, <1>sub, <1>ne, MaxBSetProperty DEF B
<1> PICK z \in GetProposals(p) : B(p) = ProposalBal(z)  BY <1>choose
<1>zgp. z \in Proposals /\ z \in Tran(p)  BY DEF GetProposals
<1>zcase. z = p \/ z \in TranExclusive(p)  BY <1>zgp DEF TranExclusive
<1>notother. z \in TranExclusive(p) => FALSE
  <2> SUFFICES ASSUME z \in TranExclusive(p) PROVE FALSE  OBVIOUS
  <2>1. z \in TranClosure(mm)  OBVIOUS
  <2>2. B(z) < b  BY <2>1
  <2>3. ProposalBal(z) <= B(z)  BY <1>zgp, ProposalBalLeB
  <2>4. ProposalBal(z) = B(p)  BY <1>choose
  <2>5. B(p) = b  OBVIOUS
  <2>zmsg. z \in Messages  BY <1>zgp, <1>propsub
  <2>pbz. ProposalBal(z) \in Ballots  BY <1>zgp, <1>tok DEF TypeOKMessageInterface
  <2>bz. B(z) \in Ballots  BY <2>zmsg, <1>tok, <1>tf, <1>anp, BBallot
  <2>bp. B(p) \in Ballots  BY <1>pm, <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>pbz, <2>bz, <2>bp DEF Ballots
<1>zisp. z = p  BY <1>zcase, <1>notother
<1> QED BY <1>choose, <1>zisp
====================================================================
