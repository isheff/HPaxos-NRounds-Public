--------------------------- MODULE ProposalBalLeB ---------------------------
EXTENDS MessageInterface, FiniteSetTheorems, MaxBSetProperty

LEMMA ProposalBalLeB ==
  ASSUME MessageInterfaceAssumptions, NEW y, y \in Proposals
  PROVE ProposalBal(y) <= B(y)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>propsub. Proposals \subseteq Messages  BY <1>tok DEF TypeOKMessageInterface
<1>ym. y \in Messages  BY <1>propsub
<1>ygp. y \in GetProposals(y)
  <2>1. y \in Tran(y)  BY DEF Tran
  <2> QED BY <2>1 DEF GetProposals
<1>fin. IsFiniteSet(GetProposals(y))
  <2>1. GetProposals(y) \subseteq Tran(y)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(y))  BY <1>ym, <1>tf DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset
<1>ne. GetProposals(y) # {}  BY <1>ygp
<1>sub. GetProposals(y) \subseteq Proposals  BY DEF GetProposals
<1>choose. /\ B(y) \in {ProposalBal(z) : z \in GetProposals(y)}
           /\ \A w \in {ProposalBal(z) : z \in GetProposals(y)} : B(y) >= w
  BY <1>tok, <1>fin, <1>sub, <1>ne, MaxBSetProperty DEF B
<1> QED BY <1>choose, <1>ygp
====================================================================
