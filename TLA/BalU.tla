--------------------------------- MODULE BalU ---------------------------------
\* Plan step (c) toward CWellFormedRec: the candidate's concrete ballot CB is
\* exactly the memo-assembled WFRBal over its priors' memos, via a Max
\* decomposition -- the per-prior proposal-ballot maxima are the priors' CBs
\* (attained and dominating, CBAttained), so the big Max over all proposals in
\* CTran(cand) collapses to the Max over {CB(p)} plus the candidate's own
\* proposal ballot (MaxDominated).  Also packages the monotonicity corollaries
\* the later candidate lemmas need.
EXTENDS WellFormedRecDef, CBuiltTran, CUnionTranFiniteClosed, CBAttained,
        CBResolve, CTranResolve, CMessageTranClosed, CMessagesSubMC,
        BalRec, CFields, MaxDominated, MaxProps, BMonotone, FiniteSetTheorems
LOCAL INSTANCE TLAPS

LEMMA BalU ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal, MessageInterface = CMI,
         NEW sdr \in CSenders, NEW pl \in CPayload,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr),
         pl \in CProposal \/ pr # {}
  PROVE LET cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
            r    == {Memo(p) : p \in pr}
        IN  /\ CB(cand) = WFRBal(pl, r)
            /\ CB(cand) \in Nat
            /\ \A p \in pr : CB(p) <= CB(cand)
            /\ \A p \in pr : \A y \in CTran(p) : CB(y) <= CB(cand)
<1> DEFINE cand  == [sender |-> sdr, payload |-> pl, priors |-> pr]
<1> DEFINE r     == {Memo(p) : p \in pr}
<1> DEFINE U     == UNION {CTran(p) : p \in pr}
<1> DEFINE OwnC  == IF pl \in CProposal THEN {pl.ballot} ELSE {}
<1> DEFINE CBals == {CB(p) : p \in pr}
<1> DEFINE DSet  == CBals \cup OwnC
<1> DEFINE Props == {y \in CTran(cand) : CIsProposal(y)}
<1> DEFINE A     == {x.payload.ballot : x \in Props}
<1>tr. CTran(cand) = {cand} \cup U /\ CTranExcl(cand) = U
  BY CBuiltTran
<1>uf. IsFiniteSet(U) /\ U \subseteq CMessages
  BY CUnionTranFiniteClosed
<1>cba. \A p \in pr :
          /\ CB(p) \in Nat
          /\ \E y \in CTran(p) : CIsProposal(y) /\ y.payload.ballot = CB(p)
          /\ \A y \in CTran(p) : CIsProposal(y) => y.payload.ballot <= CB(p)
  BY CBAttained
<1>usub. \A p \in pr : CTran(p) \subseteq U  OBVIOUS
<1>bals. {rc.bal : rc \in r} = CBals
  <2>eq. \A p \in pr : Memo(p).bal = CB(p)
    <3> SUFFICES ASSUME NEW p \in pr PROVE Memo(p).bal = CB(p)  OBVIOUS
    <3>1. p \in Messages  BY CFields
    <3>2. MemoBal(p) = B(p)  BY <3>1, BalRec
    <3>3. B(p) = CB(p)  BY CBResolve
    <3> QED BY <3>2, <3>3 DEF MemoBal
  <2>sub. {rc.bal : rc \in r} \subseteq CBals
    <3> SUFFICES ASSUME NEW rc \in r PROVE rc.bal \in CBals  OBVIOUS
    <3>1. PICK p \in pr : rc = Memo(p)  OBVIOUS
    <3> QED BY <3>1, <2>eq
  <2>sup. CBals \subseteq {rc.bal : rc \in r}
    <3> SUFFICES ASSUME NEW p \in pr PROVE CB(p) \in {rc.bal : rc \in r}
      OBVIOUS
    <3>1. Memo(p) \in r  OBVIOUS
    <3> QED BY <3>1, <2>eq
  <2> QED BY <2>sub, <2>sup
<1>cprop. CIsProposal(cand) <=> pl \in CProposal
  BY DEF CIsProposal
<1>plnat. pl \in CProposal => pl.ballot \in Nat
  <2>1. CASE pl \in CProposal
    <3>1. PICK b \in Ballots : pl = [type |-> "proposal", ballot |-> b]
      BY <2>1 DEF CProposal
    <3> QED BY <3>1 DEF Ballots
  <2> QED BY <2>1
<1>own. pl \in CProposal => pl.ballot \in A
  <2>1. CASE pl \in CProposal
    <3>1. cand \in CTran(cand)  BY <1>tr
    <3>2. cand \in Props  BY <3>1, <2>1, <1>cprop
    <3>3. cand.payload.ballot = pl.ballot  OBVIOUS
    <3> QED BY <3>2, <3>3
  <2> QED BY <2>1
<1>cbin. \A p \in pr : CB(p) \in A
  <2> SUFFICES ASSUME NEW p \in pr PROVE CB(p) \in A  OBVIOUS
  <2>1. PICK y \in CTran(p) : CIsProposal(y) /\ y.payload.ballot = CB(p)
    BY <1>cba
  <2>2. y \in U  BY <1>usub
  <2>3. y \in CTran(cand)  BY <2>2, <1>tr
  <2>4. y \in Props  BY <2>1, <2>3
  <2> QED BY <2>1, <2>4
<1>dsub. DSet \subseteq A
  <2>1. CBals \subseteq A  BY <1>cbin
  <2>2. OwnC \subseteq A  BY <1>own
  <2> QED BY <2>1, <2>2
<1>anat. \A a \in A : a \in Nat
  <2> SUFFICES ASSUME NEW x \in Props PROVE x.payload.ballot \in Nat
    OBVIOUS
  <2>1. x.payload \in CProposal  BY DEF CIsProposal
  <2>2. PICK b \in Ballots : x.payload = [type |-> "proposal", ballot |-> b]
    BY <2>1 DEF CProposal
  <2> QED BY <2>2 DEF Ballots
<1>dom. \A a \in A : \E dd \in DSet : a <= dd
  <2> SUFFICES ASSUME NEW x \in Props
      PROVE \E dd \in DSet : x.payload.ballot <= dd  OBVIOUS
  <2>xin. x \in {cand} \cup U  BY <1>tr
  <2>a. CASE x = cand
    <3>1. CIsProposal(cand)  BY <2>a
    <3>2. pl \in CProposal  BY <3>1, <1>cprop
    <3>3. pl.ballot \in OwnC  BY <3>2
    <3>4. x.payload.ballot = pl.ballot  BY <2>a
    <3>5. pl.ballot \in Nat  BY <3>2, <1>plnat
    <3> QED BY <3>3, <3>4, <3>5
  <2>b. CASE x \in U
    <3>1. PICK p \in pr : x \in CTran(p)  BY <2>b
    <3>2. CIsProposal(x)  OBVIOUS
    <3>3. x.payload.ballot <= CB(p)  BY <3>1, <3>2, <1>cba
    <3>4. CB(p) \in DSet  OBVIOUS
    <3> QED BY <3>3, <3>4
  <2> QED BY <2>a, <2>b, <2>xin
<1>afin. IsFiniteSet(A)
  <2>1. IsFiniteSet({cand} \cup U)  BY <1>uf, FS_Singleton, FS_Union
  <2>2. Props \subseteq {cand} \cup U  BY <1>tr
  <2>3. IsFiniteSet(Props)  BY <2>1, <2>2, FS_Subset
  <2> QED BY <2>3, FS_Image
<1>ane. A # {}
  <2>a. CASE pl \in CProposal  BY <2>a, <1>own
  <2>b. CASE pr # {}
    <3>1. PICK p \in pr : TRUE  BY <2>b
    <3> QED BY <3>1, <1>cbin
  <2> QED BY <2>a, <2>b
<1>meq. Max(A) = Max(DSet)
  BY <1>afin, <1>ane, <1>anat, <1>dsub, <1>dom, MaxDominated
<1>cbc. CB(cand) = Max(A)  BY DEF CB
<1>wfr. WFRBal(pl, r) = Max(DSet)  BY <1>bals DEF WFRBal
<1>c1. CB(cand) = WFRBal(pl, r)  BY <1>meq, <1>cbc, <1>wfr
<1>maxA. Max(A) \in A /\ \A y \in A : Max(A) >= y
  BY <1>afin, <1>ane, <1>anat, MaxProps
<1>c2. CB(cand) \in Nat  BY <1>maxA, <1>anat, <1>cbc
<1>c3. \A p \in pr : CB(p) <= CB(cand)
  <2> SUFFICES ASSUME NEW p \in pr PROVE CB(p) <= CB(cand)  OBVIOUS
  <2>1. CB(p) \in A  BY <1>cbin
  <2>2. Max(A) >= CB(p)  BY <2>1, <1>maxA
  <2> QED BY <2>2, <1>cbc, <1>cba, <1>c2, SMT
<1>c4. \A p \in pr : \A y \in CTran(p) : CB(y) <= CB(cand)
  <2> SUFFICES ASSUME NEW p \in pr, NEW y \in CTran(p)
      PROVE CB(y) <= CB(cand)  OBVIOUS
  <2>ym. y \in CMessages  BY CMessageTranClosed
  <2>pm. p \in Messages /\ y \in Messages  BY <2>ym, CFields
  <2>1. y \in Tran(p)  BY CTranResolve
  <2>2. B(y) <= B(p)  BY <2>pm, <2>1, BMonotone
  <2>3. B(y) = CB(y) /\ B(p) = CB(p)  BY <2>ym, CBResolve
  <2>4. CB(p) <= CB(cand)  BY <1>c3
  <2>nat. CB(y) \in Nat /\ CB(p) \in Nat /\ CB(cand) \in Nat
    BY <2>ym, CBAttained, <1>cba, <1>c2
  <2> QED BY <2>2, <2>3, <2>4, <2>nat, SMT
<1> QED BY <1>c1, <1>c2, <1>c3, <1>c4
=============================================================================
