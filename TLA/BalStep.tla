------------------------------ MODULE BalStep ------------------------------
\*   MemoRec, TranRefs, TranExclusiveRefs, TranSubMessages, BMonotone,
\*   BBallot, MaxBSetProperty, MaxProps -> cited lemmas
\*   FiniteSetTheorems -> FS_Subset, FS_Image, FS_Union, FS_Singleton,
\*                        FS_EmptySet
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, MemoRec, TranRefs, TranExclusiveCover,
        TranSubMessages, BMonotone, BBallot, MaxBSetProperty, MaxProps,
        FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* The generalized step for BalRec: given correct bal memos for ANY set S
\* between Refs(x) and TranExclusive(x), the assembly over S's memos
\* equals B(x). Squeeze: every candidate is <= B(x) (B is monotone along
\* Tran; own proposal ballot is one of B(x)'s candidates), and B(x)'s
\* achieving proposal is either x itself (own candidate) or lives in some
\* member's history (bounded by that member's B).
LEMMA BalStep ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x),
         \A p \in S : MemoBal(p) = B(p)
  PROVE BalAssemble(x, {Memo(p) : p \in S}) = B(x)
<1> DEFINE R == S
<1> DEFINE recs == {Memo(p) : p \in R}
<1> DEFINE Own == IF IsProposal(x) THEN {ProposalBal(x)} ELSE {}
<1> DEFINE BSet == {rc.bal : rc \in recs} \cup Own
<1>ih. \A p \in R : MemoBal(p) = B(p)  OBVIOUS
<1>rsub. R \subseteq TranExclusive(x)  OBVIOUS
<1>rM. R \subseteq Messages  BY <1>rsub, TranSubMessages DEF TranExclusive
<1>rT. R \subseteq Tran(x)  BY <1>rsub DEF TranExclusive
<1>idp. \A p \in R : Memo(p).bal = B(p)  BY <1>ih DEF MemoBal
<1>unfb. BalAssemble(x, recs) = Max(BSet)
  BY DEF BalAssemble
<1>bimg. {rc.bal : rc \in recs} = {B(p) : p \in R}
  <2>sub. {rc.bal : rc \in recs} \subseteq {B(p) : p \in R}
    <3> SUFFICES ASSUME NEW rc \in recs
        PROVE rc.bal \in {B(p) : p \in R}  OBVIOUS
    <3>1. PICK p \in R : rc = Memo(p)  OBVIOUS
    <3> QED BY <3>1, <1>idp
  <2>sup. {B(p) : p \in R} \subseteq {rc.bal : rc \in recs}
    <3> SUFFICES ASSUME NEW p \in R
        PROVE B(p) \in {rc.bal : rc \in recs}  OBVIOUS
    <3>1. Memo(p) \in recs  OBVIOUS
    <3> QED BY <3>1, <1>idp
  <2> QED BY <2>sub, <2>sup
<1>getx. /\ GetProposals(x) # {}
         /\ GetProposals(x) \subseteq Proposals
         /\ IsFiniteSet(GetProposals(x))
  <2>1. GetProposals(x) \subseteq Tran(x)  BY DEF GetProposals
  <2>2. IsFiniteSet(Tran(x))  BY DEF TranFinite
  <2> QED BY <2>1, <2>2, FS_Subset DEF AlwaysAProposal, GetProposals
<1>bx. /\ B(x) \in {ProposalBal(z) : z \in GetProposals(x)}
       /\ \A w \in {ProposalBal(z) : z \in GetProposals(x)} : B(x) >= w
  BY <1>getx, MaxBSetProperty DEF B
<1>bnat. B(x) \in Nat
  <2>1. B(x) \in Ballots  BY BBallot
  <2> QED BY <2>1 DEF Ballots
<1>bpnat. \A p \in R : B(p) \in Nat
  <2> SUFFICES ASSUME NEW p \in R PROVE B(p) \in Nat  OBVIOUS
  <2>1. B(p) \in Ballots  BY <1>rM, BBallot
  <2> QED BY <2>1 DEF Ballots
<1>pbx. IsProposal(x) => ProposalBal(x) \in Nat
  <2>1. CASE IsProposal(x)
    <3>1. MessageInterface.proposalbal \in [Proposals -> Ballots]
      BY DEF TypeOKMessageInterface
    <3>2. x \in Proposals  BY <2>1 DEF IsProposal
    <3> QED BY <3>1, <3>2 DEF ProposalBal, Ballots
  <2> QED BY <2>1
<1>bnats. \A v \in BSet : v \in Nat  BY <1>bimg, <1>bpnat, <1>pbx
<1>fin. IsFiniteSet(BSet)
  <2>ftx. IsFiniteSet(Tran(x))  BY DEF TranFinite
  <2>fR. IsFiniteSet(R)  BY <1>rT, <2>ftx, FS_Subset
  <2>f1. IsFiniteSet({B(p) : p \in R})  BY <2>fR, FS_Image
  <2>f2. IsFiniteSet(Own)
    <3>1. CASE IsProposal(x)  BY <3>1, FS_Singleton
    <3>2. CASE ~IsProposal(x)  BY <3>2, FS_EmptySet
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>f1, <2>f2, <1>bimg, FS_Union
<1>ne. BSet # {}
  <2>a. CASE R = {}
    <3>0. Refs(x) = {}  BY <2>a
    <3>1. Tran(x) = {x}  BY <3>0, TranRefs
    <3>2. x \in Proposals
      <4>1. GetProposals(x) \subseteq {x}  BY <3>1 DEF GetProposals
      <4> QED BY <4>1, <1>getx DEF GetProposals
    <3>3. IsProposal(x)  BY <3>2 DEF IsProposal
    <3> QED BY <3>3
  <2>b. CASE R # {}
    <3>1. PICK p \in R : TRUE  BY <2>b
    <3>2. B(p) \in {B(q) : q \in R}  BY <3>1
    <3> QED BY <3>2, <1>bimg
  <2> QED BY <2>a, <2>b
<1>mprops. Max(BSet) \in BSet /\ \A v \in BSet : Max(BSet) >= v
  BY <1>fin, <1>ne, <1>bnats, MaxProps
<1>le. \A v \in BSet : v <= B(x)
  <2> SUFFICES ASSUME NEW v \in BSet PROVE v <= B(x)  OBVIOUS
  <2>a. CASE v \in {B(p) : p \in R}
    <3>1. PICK p \in R : v = B(p)  BY <2>a
    <3>2. p \in Tran(x)  BY <1>rT
    <3>3. B(p) <= B(x)  BY <3>2, BMonotone
    <3> QED BY <3>1, <3>3
  <2>b. CASE v \in Own
    <3>1. IsProposal(x) /\ v = ProposalBal(x)  BY <2>b
    <3>2. x \in GetProposals(x)
      <4>1. x \in Tran(x)  BY DEF Tran
      <4> QED BY <4>1, <3>1 DEF GetProposals, IsProposal
    <3>3. ProposalBal(x) \in {ProposalBal(z) : z \in GetProposals(x)}
      BY <3>2
    <3> QED BY <3>1, <3>3, <1>bx
  <2> QED BY <2>a, <2>b, <1>bimg
<1>ge. \E v \in BSet : B(x) <= v
  <2>q. PICK q \in GetProposals(x) : B(x) = ProposalBal(q)  BY <1>bx
  <2>qT. q \in Tran(x) /\ q \in Proposals  BY DEF GetProposals
  <2>a. CASE q = x
    <3>1. IsProposal(x)  BY <2>a, <2>qT DEF IsProposal
    <3>2. ProposalBal(x) \in Own  BY <3>1
    <3>3. ProposalBal(x) \in BSet  BY <3>2
    <3> QED BY <2>q, <2>a, <3>3, <1>bnat, SMT
  <2>b. CASE q # x
    <3>1. q \in TranExclusive(x)  BY <2>qT, <2>b DEF TranExclusive
    <3>2. TranExclusive(x) = UNION {Tran(r) : r \in R}  BY TranExclusiveCover
    <3>3. PICK p \in R : q \in Tran(p)  BY <3>1, <3>2
    <3>4. q \in GetProposals(p)  BY <3>3, <2>qT DEF GetProposals
    <3>5. \A z \in GetProposals(p) : ProposalBal(z) <= B(p)
      <4>pM. p \in Messages  BY <1>rM
      <4>gp. /\ GetProposals(p) # {}
             /\ GetProposals(p) \subseteq Proposals
             /\ IsFiniteSet(GetProposals(p))
        <5>1. GetProposals(p) \subseteq Tran(p)  BY DEF GetProposals
        <5>2. IsFiniteSet(Tran(p))  BY <4>pM DEF TranFinite
        <5> QED BY <4>pM, <5>1, <5>2, FS_Subset
          DEF AlwaysAProposal, GetProposals
      <4>mx. \A w \in {ProposalBal(z) : z \in GetProposals(p)} : B(p) >= w
        BY <4>gp, MaxBSetProperty DEF B
      <4> QED BY <4>mx
    <3>6. ProposalBal(q) <= B(p)  BY <3>4, <3>5
    <3>7. B(p) \in BSet
      <4>1. B(p) \in {B(pp) : pp \in R}  OBVIOUS
      <4> QED BY <4>1, <1>bimg
    <3> QED BY <2>q, <3>6, <3>7
  <2> QED BY <2>a, <2>b
<1> QED
  <2>1. Max(BSet) <= B(x)  BY <1>mprops, <1>le
  <2>2. B(x) <= Max(BSet)
    <3>1. PICK v \in BSet : B(x) <= v  BY <1>ge
    <3>2. Max(BSet) >= v  BY <3>1, <1>mprops
    <3>3. v \in Nat  BY <3>1, <1>bnats
    <3>4. Max(BSet) \in Nat  BY <1>mprops, <1>bnats
    <3> QED BY <3>1, <3>2, <3>3, <3>4, <1>bnat, SMT
  <2>3. Max(BSet) \in Nat  BY <1>mprops, <1>bnats
  <2> QED BY <1>unfb, <2>1, <2>2, <2>3, <1>bnat, SMT
====================================================================
