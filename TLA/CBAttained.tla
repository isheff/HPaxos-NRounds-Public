------------------------------ MODULE CBAttained ------------------------------
\* Concrete-side reading of B's Max: at any real message, CB is attained by a
\* proposal in the closure and dominates every proposal ballot there.
EXTENDS MessageConcrete, CFields, CBResolve, CTranResolve, CMessageTranClosed,
        CProposalBalResolve, MaxBSetProperty, BBallot, FiniteSetTheorems
LOCAL INSTANCE TLAPS

LEMMA CBAttained ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         MessageInterface = CMI, NEW p \in CMessages
  PROVE /\ CB(p) \in Nat
        /\ \E y \in CTran(p) : CIsProposal(y) /\ y.payload.ballot = CB(p)
        /\ \A y \in CTran(p) : CIsProposal(y) => y.payload.ballot <= CB(p)
<1>pm. p \in Messages  BY CFields
<1>gp. /\ GetProposals(p) # {}
       /\ GetProposals(p) \subseteq Proposals
       /\ IsFiniteSet(GetProposals(p))
  <2>1. GetProposals(p) \subseteq Tran(p)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(p))  BY <1>pm DEF TranFinite
  <2> QED BY <1>pm, <2>1, <2>2, FS_Subset DEF AlwaysAProposal, GetProposals
<1>bx. /\ B(p) \in {ProposalBal(z) : z \in GetProposals(p)}
       /\ \A w \in {ProposalBal(z) : z \in GetProposals(p)} : B(p) >= w
  BY <1>gp, MaxBSetProperty DEF B
<1>gpc. GetProposals(p) = {y \in CTran(p) : CIsProposal(y)}
  <2>1. GetProposals(p) = Proposals \cap Tran(p)  BY DEF GetProposals
  <2>2. Proposals = CProposals  BY CFields
  <2>3. Tran(p) = CTran(p)  BY CTranResolve
  <2>4. CTran(p) \subseteq CMessages  BY CMessageTranClosed
  <2>5. \A y \in CTran(p) : y \in CProposals <=> CIsProposal(y)
    BY <2>4 DEF CProposals
  <2> QED BY <2>1, <2>2, <2>3, <2>5
<1>pb. \A y \in GetProposals(p) : ProposalBal(y) = y.payload.ballot
  <2> SUFFICES ASSUME NEW y \in GetProposals(p)
      PROVE ProposalBal(y) = y.payload.ballot  OBVIOUS
  <2>1. y \in CProposals  BY <1>gp, CFields DEF GetProposals
  <2> QED BY <2>1, CProposalBalResolve
<1>cb. CB(p) = B(p)  BY CBResolve
<1>nat. B(p) \in Nat
  <2>1. B(p) \in Ballots  BY <1>pm, BBallot
  <2> QED BY <2>1 DEF Ballots
<1>att. \E y \in CTran(p) : CIsProposal(y) /\ y.payload.ballot = CB(p)
  <2>1. PICK z \in GetProposals(p) : B(p) = ProposalBal(z)  BY <1>bx
  <2>2. z \in CTran(p) /\ CIsProposal(z)  BY <1>gpc
  <2>3. z.payload.ballot = B(p)  BY <2>1, <1>pb
  <2> QED BY <2>2, <2>3, <1>cb
<1>dom. \A y \in CTran(p) : CIsProposal(y) => y.payload.ballot <= CB(p)
  <2> SUFFICES ASSUME NEW y \in CTran(p), CIsProposal(y)
      PROVE y.payload.ballot <= CB(p)  OBVIOUS
  <2>1. y \in GetProposals(p)  BY <1>gpc
  <2>2. ProposalBal(y) \in {ProposalBal(z) : z \in GetProposals(p)}  BY <2>1
  <2>3. B(p) >= ProposalBal(y)  BY <2>2, <1>bx
  <2>4. ProposalBal(y) = y.payload.ballot  BY <2>1, <1>pb
  <2> QED BY <2>3, <2>4, <1>cb
<1> QED BY <1>att, <1>dom, <1>cb, <1>nat
=============================================================================
