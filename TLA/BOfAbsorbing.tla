--------------------------- MODULE BOfAbsorbing ---------------------------
EXTENDS MessageInterface, FiniteSetTheorems,
        MaxBSetProperty, ProposalBalLeB, BBallot

\* B of a non-proposal y whose exclusive ancestry S contains a proposal p at
\* the max ballot b (everything else in S strictly below b).
LEMMA BOfAbsorbing ==
  ASSUME MessageInterfaceAssumptions,
         NEW y \in Messages, NEW S \in SUBSET Messages, NEW p, NEW b \in Ballots,
         TranExclusive(y) = S, y \notin Proposals,
         p \in S, p \in Proposals, ProposalBal(p) = b,
         \A x \in S : x # p => B(x) < b
  PROVE B(y) = b
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>pty. p \in Tran(y)  BY DEF TranExclusive
<1>pgp. p \in GetProposals(y)  BY <1>pty DEF GetProposals
<1>fin. IsFiniteSet(GetProposals(y))
  <2>1. GetProposals(y) \subseteq Tran(y)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(y))  BY <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>ne. GetProposals(y) # {}  BY <1>pgp
<1>sub. GetProposals(y) \subseteq Proposals  BY DEF GetProposals
<1>choose. /\ B(y) \in {ProposalBal(z) : z \in GetProposals(y)}
           /\ \A w \in {ProposalBal(z) : z \in GetProposals(y)} : B(y) >= w
  BY <1>tok, <1>fin, <1>sub, <1>ne, MaxBSetProperty DEF B
<1>ge. B(y) >= b  BY <1>choose, <1>pgp
<1> PICK z \in GetProposals(y) : B(y) = ProposalBal(z)  BY <1>choose
<1>zgp. z \in Proposals /\ z \in Tran(y)  BY DEF GetProposals
<1>zisynotprop. z # y  BY <1>zgp
<1>zte. z \in TranExclusive(y)  BY <1>zgp, <1>zisynotprop DEF TranExclusive
<1>zinS. z \in S  BY <1>zte
<1>zbalp. B(y) = ProposalBal(z)  OBVIOUS
<1>zisp. z = p
  <2> SUFFICES ASSUME z # p PROVE FALSE  OBVIOUS
  <2>1. B(z) < b  BY <1>zinS
  <2>2. ProposalBal(z) <= B(z)  BY <1>zgp, ProposalBalLeB
  <2>zprop. z \in Proposals  BY <1>zgp
  <2>zmsg. z \in Messages  BY <2>zprop, <1>tok DEF TypeOKMessageInterface
  <2>pbz. ProposalBal(z) \in Ballots  BY <2>zprop, <1>tok DEF TypeOKMessageInterface, ProposalBal
  <2>bz. B(z) \in Ballots  BY <2>zmsg, <1>tok, <1>tf, <1>anp, BBallot
  <2>bnat. b \in Nat  BY DEF Ballots
  <2>3. B(y) < b  BY <2>1, <2>2, <1>zbalp, <2>pbz, <2>bz, <2>bnat DEF Ballots
  <2>ybal. B(y) \in Ballots  BY <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>3, <1>ge, <2>bnat, <2>ybal DEF Ballots
<1> QED BY <1>zisp
====================================================================
