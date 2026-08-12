-------------------------------- MODULE IsOneBU --------------------------------
\* Plan step (d) toward CWellFormedRec: the digest-based WFRIsOneB check on the
\* candidate's priors decides CIsOneB of the candidate record.  Candidate analog
\* of IsOneBAssembleCover: the count-2 set {z \in CTran(cand) : CB(z) =
\* CB(cand)} is exactly {cand, p*} for a witness proposal PRIOR p* -- the
\* "all other priors strictly lower" clause forces the witness maximal, and a
\* same-ballot proposal buried under a prior would surface as a third member.
EXTENDS WellFormedRecDef, BalU, CBMonotone, CBTypeNat, CBAchievedByProposal,
        CPropBalWF, CSelfInTran, DigestRec, NewBalRec, TranExclusiveRefs,
        TranSubMessages
LOCAL INSTANCE TLAPS

LEMMA IsOneBU ==
  ASSUME MessageInterfaceAssumptions, MessageInterface = CMI,
         NEW sdr \in CSenders, NEW pl \in CPayload,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr),
         pl \in CProposal \/ pr # {}
  PROVE LET cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
            r    == {Digest(p) : p \in pr}
        IN  CIsOneB(cand) <=> WFRIsOneB(pl, r)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE cand  == [sender |-> sdr, payload |-> pl, priors |-> pr]
<1> DEFINE r     == {Digest(p) : p \in pr}
<1> DEFINE U     == UNION {CTran(p) : p \in pr}
<1> DEFINE T     == {z \in CTran(cand) : CB(z) = CB(cand)}
<1> DEFINE CBals == {CB(p) : p \in pr}
<1>tr. CTran(cand) = {cand} \cup U /\ CTranExcl(cand) = U
  BY CBuiltTran
<1>uf. IsFiniteSet(U) /\ U \subseteq CMessages
  BY CUnionTranFiniteClosed
<1>candU. cand \notin U  BY <1>tr DEF CTranExcl
<1>bal. /\ CB(cand) = WFRBal(pl, r)
        /\ CB(cand) \in Nat
        /\ \A p \in pr : CB(p) <= CB(cand)
  BY <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalU
<1>idbal. \A p \in pr : Digest(p).id = p /\ Digest(p).bal = CB(p)
  <2> SUFFICES ASSUME NEW p \in pr
      PROVE Digest(p).id = p /\ Digest(p).bal = CB(p)  OBVIOUS
  <2>1. p \in Messages  BY CFields
  <2>2. Digest(p) = DigestR(p, {Digest(q) : q \in Refs(p)})
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, DigestRec
  <2>3. Digest(p).id = p  BY <2>2 DEF DigestR
  <2>4. DigestBal(p) = B(p)
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
  <2>5. B(p) = CB(p)  BY CBResolve
  <2> QED BY <2>3, <2>4, <2>5 DEF DigestBal
<1>nb. \A p \in pr : Digest(p).newbal <=> (\A y \in Refs(p) : B(y) < B(p))
  <2> SUFFICES ASSUME NEW p \in pr
      PROVE Digest(p).newbal <=> (\A y \in Refs(p) : B(y) < B(p))  OBVIOUS
  <2>1. p \in Messages  BY CFields
  <2>2. DigestNewBal(p) <=> (\A y \in Refs(p) : B(y) < B(p))
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, NewBalRec
  <2> QED BY <2>2 DEF DigestNewBal
<1>prU. \A p \in pr : p \in U /\ p \in CTran(cand)
  <2> SUFFICES ASSUME NEW p \in pr PROVE p \in U /\ p \in CTran(cand)
    OBVIOUS
  <2>1. p \in CMC  BY CMessagesSubMC
  <2>2. p \in CTran(p)  BY <2>1, CSelfInTran
  <2>3. p \in U  BY <2>2
  <2> QED BY <2>3, <1>tr
<1>cprop. CIsProposal(cand) <=> pl \in CProposal
  BY DEF CIsProposal
<1>cbnat. \A p \in pr : CB(p) \in Nat  BY CBTypeNat
<1>cbnatU. \A z \in U : CB(z) \in Nat  BY <1>uf, CBTypeNat
<1>bimg. {rc.bal : rc \in r} = CBals
  <2>sub. {rc.bal : rc \in r} \subseteq CBals
    <3> SUFFICES ASSUME NEW rc \in r PROVE rc.bal \in CBals  OBVIOUS
    <3>1. PICK p \in pr : rc = Digest(p)  OBVIOUS
    <3> QED BY <3>1, <1>idbal
  <2>sup. CBals \subseteq {rc.bal : rc \in r}
    <3> SUFFICES ASSUME NEW p \in pr PROVE CB(p) \in {rc.bal : rc \in r}
      OBVIOUS
    <3>1. Digest(p) \in r  OBVIOUS
    <3> QED BY <3>1, <1>idbal
  <2> QED BY <2>sub, <2>sup
<1>candT. cand \in T
  <2>1. cand \in CTran(cand)  BY <1>tr
  <2> QED BY <2>1
<1>finT. IsFiniteSet(T)
  <2>1. IsFiniteSet({cand} \cup U)  BY <1>uf, FS_Singleton, FS_Union
  <2>2. T \subseteq {cand} \cup U  BY <1>tr
  <2> QED BY <2>1, <2>2, FS_Subset
\* Three distinct members of T contradict Cardinality(T) = 2.
<1>T3. ASSUME NEW u1, NEW u2, u1 \in T, u2 \in T,
              u1 # u2, u1 # cand, u2 # cand,
              Cardinality(T) = 2
       PROVE FALSE
  <2>1. IsFiniteSet({u1}) /\ Cardinality({u1}) = 1  BY FS_Singleton
  <2>2. u2 \notin {u1} /\ {u1, u2} = {u1} \cup {u2}  BY <1>T3
  <2>3. IsFiniteSet({u1, u2}) /\ Cardinality({u1, u2}) = 2
    BY <2>1, <2>2, FS_AddElement
  <2>4. cand \notin {u1, u2} /\ {cand, u1, u2} = {u1, u2} \cup {cand}
    BY <1>T3
  <2>5. Cardinality({cand, u1, u2}) = 3  BY <2>3, <2>4, FS_AddElement
  <2>6. {cand, u1, u2} \subseteq T  BY <1>T3, <1>candT
  <2>7. Cardinality({cand, u1, u2}) <= Cardinality(T)
    BY <2>6, <1>finT, FS_Subset
  <2> QED BY <2>5, <2>7, <1>T3, SMT
\* ------------------------------------------------------------- forward
<1>fwd. CIsOneB(cand) => WFRIsOneB(pl, r)
  <2>1. CASE CIsOneB(cand)
    <3>np. ~CIsProposal(cand) /\ Cardinality(T) = 2  BY <2>1 DEF CIsOneB
    <3>plp. pl \notin CProposal  BY <3>np, <1>cprop
    <3>prne. pr # {}  BY <3>plp
    <3>att. \E p \in pr : CB(p) = CB(cand)
      <4>0. {rc.bal : rc \in r}
              \cup (IF pl \in CProposal THEN {pl.ballot} ELSE {}) = CBals
        BY <3>plp, <1>bimg
      <4>1. WFRBal(pl, r) = Max(CBals)  BY <4>0 DEF WFRBal
      <4>2. IsFiniteSet(CBals)  BY FS_Image
      <4>3. CBals # {}  BY <3>prne
      <4>4. \A v \in CBals : v \in Nat  BY <1>cbnat
      <4>5. Max(CBals) \in CBals  BY <4>2, <4>3, <4>4, MaxProps
      <4>6. CB(cand) = Max(CBals)  BY <4>1, <1>bal
      <4> QED BY <4>5, <4>6
    <3>p0. PICK p0 \in pr : CB(p0) = CB(cand)  BY <3>att
    <3>p0T. p0 \in T  BY <3>p0, <1>prU
    <3>p0ne. p0 # cand  BY <1>prU, <1>candU
    <3>Teq. T = {cand, p0}
      <4> SUFFICES ASSUME NEW z \in T, z # cand, z # p0 PROVE FALSE
        BY <1>candT, <3>p0T
      <4> QED BY <3>p0T, <4>, <3>p0ne, <3>np, <1>T3
    <3>p0M. p0 \in Messages  BY CFields
    <3>prop. CIsProposal(p0)
      <4>1. PICK w \in CTran(p0) : CIsProposal(w) /\ w.payload.ballot = CB(p0)
        BY CBAchievedByProposal
      <4>2. w \in CMessages
        <5>1. CTran(p0) \subseteq CMessages  BY CMessageTranClosed
        <5> QED BY <4>1, <5>1
      <4>3. CB(w) = w.payload.ballot  BY <4>1, <4>2, CPropBalWF
      <4>4. CB(w) = CB(cand)  BY <4>1, <4>3, <3>p0
      <4>5. w \in U  BY <4>1
      <4>6. w \in CTran(cand)  BY <4>5, <1>tr
      <4>7. w \in T  BY <4>4, <4>6
      <4>8. w # cand  BY <4>5, <1>candU
      <4>9. w = p0  BY <4>7, <4>8, <3>Teq
      <4> QED BY <4>1, <4>9
    <3>trp0. CTran(p0) \subseteq U  OBVIOUS
    <3>nbal. \A y \in Refs(p0) : B(y) < B(p0)
      <4> SUFFICES ASSUME NEW y \in Refs(p0) PROVE B(y) < B(p0)  OBVIOUS
      <4>1. y \in TranExclusive(p0)  BY DEF Refs
      <4>2. y \in Tran(p0) /\ y # p0  BY <4>1 DEF TranExclusive
      <4>3. Tran(p0) = CTran(p0)  BY CTranResolve
      <4>4. y \in CTran(p0)  BY <4>2, <4>3
      <4>5. y \in CMessages  BY <4>4, CMessageTranClosed
      <4>6. CB(y) <= CB(p0)  BY <4>4, CBMonotone
      <4>7. CB(y) # CB(p0)
        <5>1. CASE CB(y) = CB(p0)
          <6>1. y \in U  BY <4>4, <3>trp0
          <6>2. y \in CTran(cand)  BY <6>1, <1>tr
          <6>3. y \in T  BY <5>1, <6>2, <3>p0
          <6>4. y # cand  BY <6>1, <1>candU
          <6>5. y = p0  BY <6>3, <6>4, <3>Teq
          <6> QED BY <6>5, <4>2
        <5> QED BY <5>1
      <4>8. B(y) = CB(y) /\ B(p0) = CB(p0)  BY <4>5, CBResolve
      <4>9. CB(y) \in Nat /\ CB(p0) \in Nat  BY <4>5, CBTypeNat, <1>cbnat
      <4> QED BY <4>6, <4>7, <4>8, <4>9, SMT
    <3>c3. Digest(p0).newbal  BY <3>nbal, <1>nb
    <3>c4. \A rc2 \in r : rc2 = Digest(p0) \/ rc2.bal < WFRBal(pl, r)
      <4> SUFFICES ASSUME NEW rc2 \in r, rc2 # Digest(p0)
          PROVE rc2.bal < WFRBal(pl, r)  OBVIOUS
      <4>q. PICK q \in pr : rc2 = Digest(q)  OBVIOUS
      <4>qp. q # p0  BY <4>q, <1>idbal
      <4>1. CB(q) <= CB(cand)  BY <1>bal
      <4>2. CB(q) # CB(cand)
        <5>1. CASE CB(q) = CB(cand)
          <6>1. q \in T  BY <5>1, <1>prU
          <6>2. q # cand  BY <1>prU, <1>candU
          <6>3. q = p0  BY <6>1, <6>2, <3>Teq
          <6> QED BY <6>3, <4>qp
        <5> QED BY <5>1
      <4>3. CB(q) \in Nat  BY <1>cbnat
      <4>4. CB(q) < CB(cand)  BY <4>1, <4>2, <4>3, <1>bal, SMT
      <4> QED BY <4>q, <4>4, <1>idbal, <1>bal
    <3>fin. WFRIsOneB(pl, r)
      <4>w. Digest(p0) \in r  OBVIOUS
      <4>id. Digest(p0).id = p0  BY <1>idbal
      <4>c1. CIsProposal(Digest(p0).id)  BY <4>id, <3>prop
      <4>c2. Digest(p0).bal = WFRBal(pl, r)  BY <1>idbal, <3>p0, <1>bal
      <4> QED BY <3>plp, <4>w, <4>c1, <4>c2, <3>c3, <3>c4 DEF WFRIsOneB
    <3> QED BY <3>fin
  <2> QED BY <2>1
\* ------------------------------------------------------------ backward
<1>bwd. WFRIsOneB(pl, r) => CIsOneB(cand)
  <2>1. CASE WFRIsOneB(pl, r)
    <3>np. pl \notin CProposal  BY <2>1 DEF WFRIsOneB
    <3>rc. PICK rc \in r :
             /\ CIsProposal(rc.id)
             /\ rc.bal = WFRBal(pl, r)
             /\ rc.newbal
             /\ \A rc2 \in r : rc2 = rc \/ rc2.bal < WFRBal(pl, r)
      BY <2>1 DEF WFRIsOneB
    <3>p. PICK p \in pr : rc = Digest(p)  OBVIOUS
    <3>pM. p \in Messages  BY CFields
    <3>prop. CIsProposal(p)  BY <3>rc, <3>p, <1>idbal
    <3>pbal. CB(p) = CB(cand)  BY <3>rc, <3>p, <1>idbal, <1>bal
    <3>pT. p \in T  BY <3>pbal, <1>prU
    <3>pne. p # cand  BY <1>prU, <1>candU
    <3>newb. \A y \in Refs(p) : B(y) < B(p)  BY <3>rc, <3>p, <1>nb
    <3>texp. TranExclusive(p) = UNION {Tran(rr) : rr \in Refs(p)}
      BY <3>pM, <1>tok, <1>tf, <1>tt, <1>ta, TranExclusiveRefs
    <3>ctp. Tran(p) = CTran(p)  BY CTranResolve
    <3>sub. T \subseteq {cand, p}
      <4> SUFFICES ASSUME NEW z \in T, z # cand, z # p PROVE FALSE
        OBVIOUS
      <4>zb. z \in CTran(cand) /\ CB(z) = CB(cand)  OBVIOUS
      <4>zU. z \in U  BY <4>zb, <1>tr
      <4>zM. z \in CMessages  BY <4>zU, <1>uf
      <4>znat. CB(z) \in Nat  BY <4>zM, CBTypeNat
      <4>q. PICK q \in pr : z \in CTran(q)  BY <4>zU
      <4>a. CASE q = p
        <5>1. z \in CTran(p)  BY <4>q, <4>a
        <5>2. z \in TranExclusive(p)  BY <5>1, <3>ctp DEF TranExclusive
        <5>3. PICK rr \in Refs(p) : z \in Tran(rr)  BY <5>2, <3>texp
        <5>rrTE. rr \in TranExclusive(p)  BY <5>3 DEF Refs
        <5>rrM. rr \in Messages
          BY <5>rrTE, <3>pM, <1>tok, <1>tt, TranSubMessages
            DEF TranExclusive
        <5>4. B(z) <= B(rr)
          BY <5>3, <5>rrM, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
        <5>5. B(rr) < B(p)  BY <5>3, <3>newb
        <5>zM2. z \in Messages  BY <4>zM, CFields
        <5>6. B(z) = CB(z) /\ B(p) = CB(p)  BY <4>zM, CBResolve
        <5>7. B(rr) \in Nat
          <6>1. rr \in CMessages  BY <5>rrM, CFields
          <6> QED BY <6>1, CBResolve, CBTypeNat
        <5>8. CB(p) \in Nat  BY CBTypeNat
        <5> QED BY <4>zb, <3>pbal, <5>4, <5>5, <5>6, <5>7, <5>8, <4>znat, SMT
      <4>b. CASE q # p
        <5>1. Digest(q) \in r  OBVIOUS
        <5>2. Digest(q) # rc  BY <3>p, <1>idbal, <4>b
        <5>3. Digest(q).bal < WFRBal(pl, r)  BY <3>rc, <5>1, <5>2
        <5>4. CB(q) < CB(cand)  BY <5>3, <1>idbal, <1>bal
        <5>5. CB(z) <= CB(q)  BY <4>q, CBMonotone
        <5>6. CB(q) \in Nat  BY <1>cbnat
        <5> QED BY <4>zb, <5>4, <5>5, <5>6, <4>znat, <1>bal, SMT
      <4> QED BY <4>a, <4>b
    <3>eq. T = {cand, p}  BY <3>sub, <1>candT, <3>pT
    <3>card. Cardinality(T) = 2
      <4>1. IsFiniteSet({p}) /\ Cardinality({p}) = 1  BY FS_Singleton
      <4>2. cand \notin {p}  BY <3>pne
      <4>3. {cand, p} = {p} \cup {cand}  OBVIOUS
      <4> QED BY <4>1, <4>2, <4>3, <3>eq, FS_AddElement
    <3> QED BY <3>np, <1>cprop, <3>card DEF CIsOneB
  <2> QED BY <2>1
<1> QED BY <1>fwd, <1>bwd
=============================================================================
