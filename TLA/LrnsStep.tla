------------------------------ MODULE LrnsStep ------------------------------
\*   DigestRec, BalRec, AttesterInherit, HasDepthDef, HasDepthDownward,
\*   QuorumsHaveMembers, TranExclusiveRefs, TranSubMessages, BMonotone,
\*   BBallot, MaxProps -> cited lemmas
\*   FiniteSetTheorems -> FS_Subset, FS_Image
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, DigestRec, BalStep, BalRec, AttesterInherit,
        HasDepthDef, HasDepthDownward, QuorumsHaveMembers, TranExclusiveCover,
        TranSubMessages, BMonotone, BBallot, MaxProps, FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* The step for the lrns part of DigestInv: given the refs' accumulators,
\* the assembled lrns is exactly Lrns(x) = {alpha : HasDepth(alpha, x, 1)}.
\* Frontier >= 1: acceptor-signedness suffices (inherit the frontier
\* attester's quorum, then step down to level 1). Frontier 0: exactly the
\* Bump check (the pending set IS Qd(alpha, x, 1)). No frontier: no
\* level-0 attesters, and quorums are never empty.
LEMMA LrnsStep ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x),
         \A p \in S : MaxQDepthInvariant(p)
  PROVE LrnsAssemble(x, {Digest(p) : p \in S}) = Lrns(x)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE R == S
<1> DEFINE recs == {Digest(p) : p \in R}
<1>ih. \A p \in R : MaxQDepthInvariant(p)  OBVIOUS
<1>rsub. R \subseteq TranExclusive(x)  OBVIOUS
<1>rM. R \subseteq Messages
  BY <1>rsub, <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>tex. TranExclusive(x) = UNION {Tran(p) : p \in R}
  BY <1>tok, <1>tf, <1>tt, <1>ta, TranExclusiveCover
<1>texP. \A p \in R : Tran(p) \subseteq TranExclusive(x)  BY <1>tex
<1>pTE. \A p \in R : p \in TranExclusive(x)  BY <1>rsub
<1>idp. \A p \in R : /\ Digest(p).id = p
                     /\ Digest(p).bal = B(p)
                     /\ Digest(p).maxqdepth = DigestMaxQDepth(p)
                     /\ Digest(p).pendingqd = DigestPendingQd(p)
  <2> SUFFICES ASSUME NEW p \in R
      PROVE /\ Digest(p).id = p
            /\ Digest(p).bal = B(p)
            /\ Digest(p).maxqdepth = DigestMaxQDepth(p)
            /\ Digest(p).pendingqd = DigestPendingQd(p)
    OBVIOUS
  <2>1. p \in Messages  BY <1>rM
  <2>2. Digest(p) = DigestR(p, {Digest(q) : q \in Refs(p)})
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, DigestRec
  <2>3. DigestBal(p) = B(p)
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
  <2> QED BY <2>2, <2>3
    DEF DigestR, DigestBal, DigestMaxQDepth, DigestPendingQd
<1>bal. BalAssemble(x, recs) = B(x)
  <2>1. \A p \in R : DigestBal(p) = B(p)
    BY <1>rM, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
  <2> QED BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalStep
<1>sbref. \A p \in R : (Digest(p) \in SBRefs(x, recs)) <=> (B(p) = B(x))
  BY <1>idp, <1>bal DEF SBRefs
<1>sbpick. \A rc \in SBRefs(x, recs) : \E p \in R : rc = Digest(p) /\ B(p) = B(x)
  <2> SUFFICES ASSUME NEW rc \in SBRefs(x, recs)
      PROVE \E p \in R : rc = Digest(p) /\ B(p) = B(x)
    OBVIOUS
  <2>1. rc \in recs /\ rc.bal = BalAssemble(x, recs)  BY DEF SBRefs
  <2>2. PICK p \in R : rc = Digest(p)  BY <2>1
  <2> QED BY <2>1, <2>2, <1>idp, <1>bal
<1>tnat. \A y \in Tran(x) : B(y) \in Nat
  <2> SUFFICES ASSUME NEW y \in Tran(x) PROVE B(y) \in Nat  OBVIOUS
  <2>1. y \in Messages  BY <1>tok, <1>tt, TranSubMessages
  <2>2. B(y) \in Ballots  BY <2>1, <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>2 DEF Ballots
<1>same. \A y \in TranExclusive(x) :
           B(y) = B(x) => \E p \in R : B(p) = B(x) /\ y \in Tran(p)
  <2> SUFFICES ASSUME NEW y \in TranExclusive(x), B(y) = B(x)
      PROVE \E p \in R : B(p) = B(x) /\ y \in Tran(p)
    OBVIOUS
  <2>p. PICK p \in R : y \in Tran(p)  BY <1>tex
  <2>pM. p \in Messages  BY <1>rM
  <2>1. B(y) <= B(p)
    BY <2>p, <2>pM, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
  <2>2. B(p) <= B(x)
    <3>1. p \in Tran(x)  BY <1>pTE DEF TranExclusive
    <3> QED BY <3>1, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
  <2>3. B(p) \in Nat /\ B(y) \in Nat /\ B(x) \in Nat
    <3>1. p \in Tran(x) /\ y \in Tran(x) /\ x \in Tran(x)
      BY <1>pTE DEF TranExclusive, Tran
    <3> QED BY <3>1, <1>tnat
  <2>4. B(p) = B(x)  BY <2>1, <2>2, <2>3, SMT
  <2> QED BY <2>p, <2>4
<1>qdomchar. \A al \in Learners :
    al \in QDom(x, recs)
    <=> (\E y \in TranExclusive(x) :
           B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d))
  <2> SUFFICES ASSUME NEW al \in Learners
      PROVE al \in QDom(x, recs)
              <=> (\E y \in TranExclusive(x) :
                     B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d))
    OBVIOUS
  <2>fwd. al \in QDom(x, recs) =>
            \E y \in TranExclusive(x) :
              B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d)
    <3>1. CASE al \in QDom(x, recs)
      <4>1. PICK rc \in SBRefs(x, recs) : al \in DOMAIN rc.maxqdepth
        BY <3>1 DEF QDom
      <4>2. PICK p \in R : rc = Digest(p) /\ B(p) = B(x)  BY <4>1, <1>sbpick
      <4>3. al \in DOMAIN DigestMaxQDepth(p)  BY <4>1, <4>2, <1>idp
      <4>4. \E y \in Tran(p) : B(y) = B(p) /\ \E d \in Nat : HasDepth(al, y, d)
        BY <4>2, <4>3, <1>ih DEF MaxQDepthInvariant
      <4>5. PICK y \in Tran(p) : B(y) = B(p) /\ \E d \in Nat : HasDepth(al, y, d)
        BY <4>4
      <4>6. y \in TranExclusive(x)  BY <4>2, <4>5, <1>texP
      <4> QED BY <4>2, <4>5, <4>6
    <3> QED BY <3>1
  <2>bwd. (\E y \in TranExclusive(x) :
             B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d))
          => al \in QDom(x, recs)
    <3>1. CASE \E y \in TranExclusive(x) :
                 B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d)
      <4>y. PICK y \in TranExclusive(x) :
              B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d)
        BY <3>1
      <4>p. PICK p \in R : B(p) = B(x) /\ y \in Tran(p)  BY <4>y, <1>same
      <4>1. al \in {a2 \in Learners :
                      \E yy \in Tran(p) :
                        B(yy) = B(p) /\ \E d \in Nat : HasDepth(a2, yy, d)}
        BY <4>y, <4>p
      <4>2. al \in DOMAIN DigestMaxQDepth(p)
        BY <4>1, <4>p, <1>ih DEF MaxQDepthInvariant
      <4>3. Digest(p) \in SBRefs(x, recs)  BY <4>p, <1>sbref
      <4>4. al \in DOMAIN Digest(p).maxqdepth  BY <4>2, <1>idp
      <4> QED BY <4>3, <4>4 DEF QDom
    <3> QED BY <3>1
  <2> QED BY <2>fwd, <2>bwd
<1>iff. \A al \in Learners :
          al \in LrnsAssemble(x, recs) <=> HasDepth(al, x, 1)
  <2> SUFFICES ASSUME NEW al \in Learners
      PROVE al \in LrnsAssemble(x, recs) <=> HasDepth(al, x, 1)
    OBVIOUS
  <2>hd1. HasDepth(al, x, 1) =
            (/\ Sig(x) \in Acceptors
             /\ SigS(Qd(al, x, 1)) \in Quorums(al))
    <3>1. HasDepth(al, x, 1) =
            (/\ Sig(x) \in Acceptors
             /\ IF 1 = 0 THEN (IsOneB(x) /\ Fresh(al, x))
                         ELSE SigS(Qd(al, x, 1)) \in Quorums(al))
      BY <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDef
    <3> QED BY <3>1
  <2>A. CASE al \in QDom(x, recs)
    <3>cne. QDepthCands(al, x, recs) # {}
      <4>1. PICK rc \in SBRefs(x, recs) : al \in DOMAIN rc.maxqdepth
        BY <2>A DEF QDom
      <4>2. rc \in {y \in SBRefs(x, recs) : al \in DOMAIN y.maxqdepth}
        BY <4>1
      <4> QED BY <4>2 DEF QDepthCands, QDepthCand
    <3>cnat. \A v \in QDepthCands(al, x, recs) : v \in Nat
      <4> SUFFICES ASSUME NEW v \in QDepthCands(al, x, recs)
          PROVE v \in Nat  OBVIOUS
      <4>1. PICK rc \in {y \in SBRefs(x, recs) : al \in DOMAIN y.maxqdepth} :
              v = QDepthCand(al, rc)
        BY DEF QDepthCands
      <4>2. PICK p \in R : rc = Digest(p) /\ B(p) = B(x)  BY <4>1, <1>sbpick
      <4>3. al \in DOMAIN DigestMaxQDepth(p)  BY <4>1, <4>2, <1>idp
      <4>4. v = DigestMaxQDepth(p)[al]  BY <4>1, <4>2, <1>idp DEF QDepthCand
      <4> QED BY <4>3, <4>4, <4>2, <1>ih DEF MaxQDepthInvariant
    <3>cfin. IsFiniteSet(QDepthCands(al, x, recs))
      <4>ftx. IsFiniteSet(Tran(x))  BY <1>tf DEF TranFinite
      <4>fR. IsFiniteSet(R)
        <5>1. R \subseteq Tran(x)  BY <1>rsub DEF TranExclusive
        <5> QED BY <5>1, <4>ftx, FS_Subset
      <4>frecs. IsFiniteSet(recs)  BY <4>fR, FS_Image
      <4>f1. IsFiniteSet(SBRefs(x, recs))  BY <4>frecs, FS_Subset DEF SBRefs
      <4>f2. IsFiniteSet({y \in SBRefs(x, recs) : al \in DOMAIN y.maxqdepth})
        BY <4>f1, FS_Subset
      <4> QED BY <4>f2, FS_Image DEF QDepthCands
    <3>D0. /\ RefFrontier(al, x, recs) \in QDepthCands(al, x, recs)
           /\ \A v \in QDepthCands(al, x, recs) : RefFrontier(al, x, recs) >= v
      BY <3>cne, <3>cnat, <3>cfin, MaxProps DEF RefFrontier
    <3>D0nat. RefFrontier(al, x, recs) \in Nat  BY <3>D0, <3>cnat
    <3>pcand. \A p \in R : (B(p) = B(x) /\ al \in DOMAIN DigestMaxQDepth(p)) =>
                DigestMaxQDepth(p)[al] \in QDepthCands(al, x, recs)
      <4> SUFFICES ASSUME NEW p \in R, B(p) = B(x),
                          al \in DOMAIN DigestMaxQDepth(p)
          PROVE DigestMaxQDepth(p)[al] \in QDepthCands(al, x, recs)
        OBVIOUS
      <4>1. Digest(p) \in SBRefs(x, recs)  BY <1>sbref
      <4>2. al \in DOMAIN Digest(p).maxqdepth  BY <1>idp
      <4>3. Digest(p) \in {y \in SBRefs(x, recs) : al \in DOMAIN y.maxqdepth}
        BY <4>1, <4>2
      <4>4. QDepthCand(al, Digest(p)) = DigestMaxQDepth(p)[al]
        BY <1>idp DEF QDepthCand
      <4> QED BY <4>3, <4>4 DEF QDepthCands
    <3>att0. \E y \in TranExclusive(x) :
               B(y) = B(x) /\ HasDepth(al, y, RefFrontier(al, x, recs))
      <4>1. PICK rc \in {y \in SBRefs(x, recs) : al \in DOMAIN y.maxqdepth} :
              RefFrontier(al, x, recs) = QDepthCand(al, rc)
        BY <3>D0 DEF QDepthCands
      <4>2. PICK p \in R : rc = Digest(p) /\ B(p) = B(x)  BY <4>1, <1>sbpick
      <4>3. al \in DOMAIN DigestMaxQDepth(p)  BY <4>1, <4>2, <1>idp
      <4>4. RefFrontier(al, x, recs) = DigestMaxQDepth(p)[al]
        BY <4>1, <4>2, <1>idp DEF QDepthCand
      <4>5. \E y \in Tran(p) :
              B(y) = B(p) /\ HasDepth(al, y, DigestMaxQDepth(p)[al])
        BY <4>2, <4>3, <1>ih DEF MaxQDepthInvariant
      <4>6. PICK y \in Tran(p) :
              B(y) = B(p) /\ HasDepth(al, y, DigestMaxQDepth(p)[al])
        BY <4>5
      <4> QED BY <4>2, <4>4, <4>6, <1>texP
    <3>P0. RefPending(al, x, recs)
             = {y \in TranExclusive(x) :
                  B(y) = B(x) /\ HasDepth(al, y, RefFrontier(al, x, recs))}
      <4>sub. RefPending(al, x, recs) \subseteq
                {y \in TranExclusive(x) :
                   B(y) = B(x) /\ HasDepth(al, y, RefFrontier(al, x, recs))}
        <5> SUFFICES ASSUME NEW y \in RefPending(al, x, recs)
            PROVE y \in {yy \in TranExclusive(x) :
                           B(yy) = B(x)
                           /\ HasDepth(al, yy, RefFrontier(al, x, recs))}
          OBVIOUS
        <5>1. PICK rc \in {z \in SBRefs(x, recs) :
                             /\ al \in DOMAIN z.maxqdepth
                             /\ z.maxqdepth[al] = RefFrontier(al, x, recs)} :
                y \in RefPendingPart(al, rc)
          BY DEF RefPending
        <5>2. PICK p \in R : rc = Digest(p) /\ B(p) = B(x)  BY <5>1, <1>sbpick
        <5>3. al \in DOMAIN DigestMaxQDepth(p)
                /\ DigestMaxQDepth(p)[al] = RefFrontier(al, x, recs)
          BY <5>1, <5>2, <1>idp
        <5>4. y \in DigestPendingQd(p)[al]
          BY <5>1, <5>2, <1>idp DEF RefPendingPart
        <5>5. DigestPendingQd(p)[al]
                = {yy \in Tran(p) :
                     B(yy) = B(p) /\ HasDepth(al, yy, DigestMaxQDepth(p)[al])}
          BY <5>2, <5>3, <1>ih DEF MaxQDepthInvariant
        <5>6. y \in Tran(p) /\ B(y) = B(p)
                /\ HasDepth(al, y, RefFrontier(al, x, recs))
          BY <5>4, <5>5, <5>3
        <5> QED BY <5>2, <5>6, <1>texP
      <4>sup. {y \in TranExclusive(x) :
                 B(y) = B(x) /\ HasDepth(al, y, RefFrontier(al, x, recs))}
                \subseteq RefPending(al, x, recs)
        <5> SUFFICES ASSUME NEW y \in TranExclusive(x), B(y) = B(x),
                            HasDepth(al, y, RefFrontier(al, x, recs))
            PROVE y \in RefPending(al, x, recs)
          OBVIOUS
        <5>p. PICK p \in R : B(p) = B(x) /\ y \in Tran(p)  BY <1>same
        <5>dom. al \in DOMAIN DigestMaxQDepth(p)
          <6>1. al \in {a2 \in Learners :
                          \E yy \in Tran(p) :
                            B(yy) = B(p) /\ \E dd \in Nat : HasDepth(a2, yy, dd)}
            BY <5>p, <3>D0nat
          <6> QED BY <6>1, <5>p, <1>ih DEF MaxQDepthInvariant
        <5>ge. RefFrontier(al, x, recs) <= DigestMaxQDepth(p)[al]
          BY <5>p, <5>dom, <3>D0nat, <1>ih DEF MaxQDepthInvariant
        <5>le. DigestMaxQDepth(p)[al] <= RefFrontier(al, x, recs)
          <6>1. DigestMaxQDepth(p)[al] \in QDepthCands(al, x, recs)
            BY <5>p, <5>dom, <3>pcand
          <6> QED BY <6>1, <3>D0
        <5>nat. DigestMaxQDepth(p)[al] \in Nat
          BY <5>p, <5>dom, <1>ih DEF MaxQDepthInvariant
        <5>eq. DigestMaxQDepth(p)[al] = RefFrontier(al, x, recs)
          BY <5>ge, <5>le, <5>nat, <3>D0nat, SMT
        <5>mem. y \in DigestPendingQd(p)[al]
          <6>1. DigestPendingQd(p)[al]
                  = {yy \in Tran(p) :
                       B(yy) = B(p) /\ HasDepth(al, yy, DigestMaxQDepth(p)[al])}
            BY <5>p, <5>dom, <1>ih DEF MaxQDepthInvariant
          <6> QED BY <6>1, <5>p, <5>eq
        <5>flt. Digest(p) \in {z \in SBRefs(x, recs) :
                                 /\ al \in DOMAIN z.maxqdepth
                                 /\ z.maxqdepth[al] = RefFrontier(al, x, recs)}
          <6>1. Digest(p) \in SBRefs(x, recs)  BY <5>p, <1>sbref
          <6> QED BY <6>1, <5>dom, <5>eq, <1>idp
        <5>part. y \in RefPendingPart(al, Digest(p))
          BY <5>mem, <1>idp DEF RefPendingPart
        <5> QED BY <5>flt, <5>part DEF RefPending
      <4> QED BY <4>sub, <4>sup
    <3>mem. al \in LrnsAssemble(x, recs)
              <=> (IF RefFrontier(al, x, recs) >= 1
                     THEN Sig(x) \in Acceptors
                     ELSE Bump(al, x, recs))
      BY <2>A DEF LrnsAssemble
    <3>a. CASE RefFrontier(al, x, recs) >= 1
      <4>fwd. Sig(x) \in Acceptors => HasDepth(al, x, 1)
        <5>1. CASE Sig(x) \in Acceptors
          <6>1. PICK y \in TranExclusive(x) :
                  B(y) = B(x) /\ HasDepth(al, y, RefFrontier(al, x, recs))
            BY <3>att0
          <6>2. HasDepth(al, x, RefFrontier(al, x, recs))
            BY <5>1, <6>1, <3>a, <3>D0nat,
               <1>tok, <1>tt, <1>tf, <1>ta, AttesterInherit
          <6>3. HasDepth(al, x, 1)
            BY <6>2, <3>a, <3>D0nat,
               <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDownward
          <6> QED BY <6>3
        <5> QED BY <5>1
      <4>bwd. HasDepth(al, x, 1) => Sig(x) \in Acceptors  BY <2>hd1
      <4> QED BY <3>mem, <3>a, <4>fwd, <4>bwd
    <3>b. CASE ~(RefFrontier(al, x, recs) >= 1)
      <4>d0. RefFrontier(al, x, recs) = 0  BY <3>b, <3>D0nat, SMT
      <4>qd1. Qd(al, x, 1) = RefPending(al, x, recs)
        <5>ar. 1 > 0 /\ 1 - 1 = 0  BY SMT
        <5>sub. Qd(al, x, 1) \subseteq RefPending(al, x, recs)
          <6> SUFFICES ASSUME NEW z \in Qd(al, x, 1)
              PROVE z \in RefPending(al, x, recs)  OBVIOUS
          <6>1. z \in TranExclusive(x) /\ B(x) = B(z)
                  /\ HasDepth(al, z, 1 - 1)
            BY DEF Qd
          <6>2. HasDepth(al, z, RefFrontier(al, x, recs))
            BY <6>1, <5>ar, <4>d0
          <6> QED BY <6>1, <6>2, <3>P0
        <5>sup. RefPending(al, x, recs) \subseteq Qd(al, x, 1)
          <6> SUFFICES ASSUME NEW z \in RefPending(al, x, recs)
              PROVE z \in Qd(al, x, 1)  OBVIOUS
          <6>1. z \in TranExclusive(x) /\ B(z) = B(x)
                  /\ HasDepth(al, z, RefFrontier(al, x, recs))
            BY <3>P0
          <6>2. HasDepth(al, z, 1 - 1)  BY <6>1, <5>ar, <4>d0
          <6> QED BY <6>1, <6>2, <5>ar DEF Qd
        <5> QED BY <5>sub, <5>sup
      <4>fwd. Bump(al, x, recs) => HasDepth(al, x, 1)
        <5>1. CASE Bump(al, x, recs)
          <6>1. Sig(x) \in Acceptors
                  /\ SigS(RefPending(al, x, recs)) \in Quorums(al)
            BY <5>1 DEF Bump
          <6>2. SigS(Qd(al, x, 1)) \in Quorums(al)  BY <6>1, <4>qd1
          <6> QED BY <6>1, <6>2, <2>hd1
        <5> QED BY <5>1
      <4>bwd. HasDepth(al, x, 1) => Bump(al, x, recs)
        <5>1. CASE HasDepth(al, x, 1)
          <6>1. Sig(x) \in Acceptors /\ SigS(Qd(al, x, 1)) \in Quorums(al)
            BY <5>1, <2>hd1
          <6>2. SigS(RefPending(al, x, recs)) \in Quorums(al)
            BY <6>1, <4>qd1
          <6> QED BY <6>1, <6>2 DEF Bump
        <5> QED BY <5>1
      <4> QED BY <3>mem, <3>b, <4>fwd, <4>bwd
    <3> QED BY <3>a, <3>b
  <2>B. CASE al \notin QDom(x, recs)
    <3>1. al \notin LrnsAssemble(x, recs)  BY <2>B DEF LrnsAssemble
    <3>2. ~HasDepth(al, x, 1)
      <4>1. CASE HasDepth(al, x, 1)
        <5>1. SigS(Qd(al, x, 1)) \in Quorums(al)  BY <4>1, <2>hd1
        <5>2. SigS(Qd(al, x, 1)) # {}  BY <5>1, QuorumsHaveMembers
        <5>3. Qd(al, x, 1) # {}  BY <5>2 DEF SigS
        <5>4. PICK z \in Qd(al, x, 1) : TRUE  BY <5>3
        <5>5. z \in TranExclusive(x) /\ B(x) = B(z)
                /\ HasDepth(al, z, 1 - 1)
          BY <5>4 DEF Qd
        <5>6. 1 - 1 \in Nat  BY SMT
        <5>7. al \in QDom(x, recs)  BY <5>5, <5>6, <1>qdomchar
        <5> QED BY <5>7, <2>B
      <4> QED BY <4>1
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>A, <2>B
<1>lsub. LrnsAssemble(x, recs) \subseteq Learners
  BY DEF LrnsAssemble, QDom
<1>ldef. Lrns(x) = {al \in Learners : HasDepth(al, x, 1)}  BY DEF Lrns
<1> QED
  <2>sub. LrnsAssemble(x, recs) \subseteq Lrns(x)
    <3> SUFFICES ASSUME NEW al \in LrnsAssemble(x, recs)
        PROVE al \in Lrns(x)  OBVIOUS
    <3>1. al \in Learners  BY <1>lsub
    <3>2. HasDepth(al, x, 1)  BY <3>1, <1>iff
    <3> QED BY <3>1, <3>2, <1>ldef
  <2>sup. Lrns(x) \subseteq LrnsAssemble(x, recs)
    <3> SUFFICES ASSUME NEW al \in Lrns(x)
        PROVE al \in LrnsAssemble(x, recs)  OBVIOUS
    <3>1. al \in Learners /\ HasDepth(al, x, 1)  BY <1>ldef
    <3> QED BY <3>1, <1>iff
  <2> QED BY <2>sub, <2>sup
====================================================================
