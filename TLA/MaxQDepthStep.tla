---------------------------- MODULE MaxQDepthStep ----------------------------
\*   MemoRec, BalRec, IsOneBMemo, FreshRec, AttesterInherit,
\*   HasDepthDef, QuorumsHaveMembers, TranExclusiveRefs, TranSubMessages,
\*   BMonotone, BBallot, MaxProps -> cited lemmas
\*   FiniteSetTheorems -> FS_Subset, FS_Image
\*   TLAPS -> SMT; proof-only
EXTENDS RecursiveWellFormed, MemoRec, BalStep, BalRec, IsOneBAssembleCover,
        AttesterInherit, HasDepthDef, QuorumsHaveMembers, TranExclusiveCover,
        TranSubMessages, BMonotone, BBallot, MaxProps, FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* The generalized step for the maxqdepth/pendingqd part of MemoInv:
\* given correct accumulator memos for ANY set S between Refs(x) and
\* TranExclusive(x), and the correctness of the fresh check over S
\* (supplied by the combined induction via FreshResolve), the accumulator
\* assembled over S's memos is correct for x.
LEMMA MaxQDepthStep ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x),
         \A alpha \in Learners :
           FreshAssemble(alpha, x, {Memo(p) : p \in S}) <=> Fresh(alpha, x),
         \A p \in S : MaxQDepthInvariant(p)
  PROVE MaxQDepthCorrect(x, MaxQDepthAssemble(x, {Memo(p) : p \in S}),
                         PendingQdAssemble(x, {Memo(p) : p \in S}))
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE R == S
<1> DEFINE recs == {Memo(p) : p \in R}
<1> DEFINE mqA == MaxQDepthAssemble(x, recs)
<1> DEFINE pqA == PendingQdAssemble(x, recs)
<1>ih. \A p \in R : MaxQDepthInvariant(p)  OBVIOUS
<1>rsub. R \subseteq TranExclusive(x)  OBVIOUS
<1>rM. R \subseteq Messages
  BY <1>rsub, <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>tex. TranExclusive(x) = UNION {Tran(p) : p \in R}
  BY <1>tok, <1>tf, <1>tt, <1>ta, TranExclusiveCover
<1>texP. \A p \in R : Tran(p) \subseteq TranExclusive(x)  BY <1>tex
<1>pTE. \A p \in R : p \in TranExclusive(x)  BY <1>rsub
<1>teM. TranExclusive(x) \subseteq Messages
  BY <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>idp. \A p \in R : /\ Memo(p).id = p
                     /\ Memo(p).bal = B(p)
                     /\ Memo(p).maxqdepth = MemoMaxQDepth(p)
                     /\ Memo(p).pendingqd = MemoPendingQd(p)
  <2> SUFFICES ASSUME NEW p \in R
      PROVE /\ Memo(p).id = p
            /\ Memo(p).bal = B(p)
            /\ Memo(p).maxqdepth = MemoMaxQDepth(p)
            /\ Memo(p).pendingqd = MemoPendingQd(p)
    OBVIOUS
  <2>1. p \in Messages  BY <1>rM
  <2>2. Memo(p) = MemoR(p, {Memo(q) : q \in Refs(p)})
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, MemoRec
  <2>3. MemoBal(p) = B(p)
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
  <2> QED BY <2>2, <2>3
    DEF MemoR, MemoBal, MemoMaxQDepth, MemoPendingQd
<1>bal. BalAssemble(x, recs) = B(x)
  <2>1. \A p \in R : MemoBal(p) = B(p)
    BY <1>rM, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
  <2> QED BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalStep
<1>l0. \A al \in Learners :
         SelfL0(al, x, recs) <=> (Sig(x) \in Acceptors /\ IsOneB(x) /\ Fresh(al, x))
  <2>io. IsOneBAssemble(x, recs) <=> IsOneB(x)
    BY IsOneBAssembleCover
  <2>fr. \A al \in Learners : FreshAssemble(al, x, recs) <=> Fresh(al, x)
    OBVIOUS
  <2> QED BY <2>io, <2>fr DEF SelfL0
<1>x0equiv. \A al \in Learners : HasDepth(al, x, 0) <=> SelfL0(al, x, recs)
  <2> SUFFICES ASSUME NEW al \in Learners
      PROVE HasDepth(al, x, 0) <=> SelfL0(al, x, recs)  OBVIOUS
  <2>1. HasDepth(al, x, 0) =
          (/\ Sig(x) \in Acceptors
           /\ IF 0 = 0 THEN (IsOneB(x) /\ Fresh(al, x))
                       ELSE SigS(Qd(al, x, 0)) \in Quorums(al))
    BY <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDef
  <2> QED BY <2>1, <1>l0
<1>sbref. \A p \in R : (Memo(p) \in SBRefs(x, recs)) <=> (B(p) = B(x))
  BY <1>idp, <1>bal DEF SBRefs
<1>sbpick. \A rc \in SBRefs(x, recs) : \E p \in R : rc = Memo(p) /\ B(p) = B(x)
  <2> SUFFICES ASSUME NEW rc \in SBRefs(x, recs)
      PROVE \E p \in R : rc = Memo(p) /\ B(p) = B(x)
    OBVIOUS
  <2>1. rc \in recs /\ rc.bal = BalAssemble(x, recs)  BY DEF SBRefs
  <2>2. PICK p \in R : rc = Memo(p)  BY <2>1
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
      <4>2. PICK p \in R : rc = Memo(p) /\ B(p) = B(x)  BY <4>1, <1>sbpick
      <4>3. al \in DOMAIN MemoMaxQDepth(p)  BY <4>1, <4>2, <1>idp
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
      <4>2. al \in DOMAIN MemoMaxQDepth(p)
        BY <4>1, <1>ih DEF MaxQDepthInvariant
      <4>3. Memo(p) \in SBRefs(x, recs)  BY <4>p, <1>sbref
      <4>4. al \in DOMAIN Memo(p).maxqdepth  BY <4>2, <1>idp
      <4> QED BY <4>3, <4>4 DEF QDom
    <3> QED BY <3>1
  <2> QED BY <2>fwd, <2>bwd
<1>dommx. DOMAIN mqA = MQDomain(x, recs)
  BY DEF MaxQDepthAssemble
<1>dompd. DOMAIN pqA = MQDomain(x, recs)
  BY DEF PendingQdAssemble
<1>dom. DOMAIN mqA
          = {al \in Learners :
               \E y \in Tran(x) : B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d)}
  <2>sub. MQDomain(x, recs) \subseteq
            {al \in Learners :
               \E y \in Tran(x) : B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d)}
    <3> SUFFICES ASSUME NEW al \in MQDomain(x, recs)
        PROVE al \in {a2 \in Learners :
                        \E y \in Tran(x) :
                          B(y) = B(x) /\ \E d \in Nat : HasDepth(a2, y, d)}
      OBVIOUS
    <3>L. al \in Learners  BY DEF MQDomain, QDom
    <3>a. CASE al \in QDom(x, recs)
      <4>1. \E y \in TranExclusive(x) :
              B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d)
        BY <3>a, <3>L, <1>qdomchar
      <4> QED BY <4>1, <3>L DEF TranExclusive
    <3>b. CASE al \notin QDom(x, recs)
      <4>1. SelfL0(al, x, recs)  BY <3>b DEF MQDomain
      <4>2. HasDepth(al, x, 0)  BY <4>1, <3>L, <1>x0equiv
      <4>3. x \in Tran(x)  BY DEF Tran
      <4> QED BY <4>2, <4>3, <3>L
    <3> QED BY <3>a, <3>b
  <2>sup. {al \in Learners :
             \E y \in Tran(x) : B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d)}
            \subseteq MQDomain(x, recs)
    <3> SUFFICES ASSUME NEW al \in Learners,
                        NEW y \in Tran(x), B(y) = B(x),
                        NEW d \in Nat, HasDepth(al, y, d)
        PROVE al \in MQDomain(x, recs)
      OBVIOUS
    <3>a. CASE y # x
      <4>1. y \in TranExclusive(x)  BY <3>a DEF TranExclusive
      <4>2. al \in QDom(x, recs)  BY <4>1, <1>qdomchar
      <4> QED BY <4>2 DEF MQDomain
    <3>b. CASE y = x
      <4>a. CASE al \in QDom(x, recs)
        <5> QED BY <4>a DEF MQDomain
      <4>b. CASE al \notin QDom(x, recs)
        <5>d0. d = 0
          <6>1. CASE d # 0
            <7>1. SigS(Qd(al, x, d)) \in Quorums(al)
              <8>1. HasDepth(al, x, d) =
                      (/\ Sig(x) \in Acceptors
                       /\ IF d = 0 THEN (IsOneB(x) /\ Fresh(al, x))
                                   ELSE SigS(Qd(al, x, d)) \in Quorums(al))
                BY <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDef
              <8> QED BY <8>1, <3>b, <6>1
            <7>2. SigS(Qd(al, x, d)) # {}
              BY <7>1, QuorumsHaveMembers
            <7>3. Qd(al, x, d) # {}  BY <7>2 DEF SigS
            <7>4. PICK z \in Qd(al, x, d) : TRUE  BY <7>3
            <7>5. z \in TranExclusive(x) /\ B(x) = B(z)
                    /\ HasDepth(al, z, d - 1)
              BY <7>4 DEF Qd
            <7>6. d - 1 \in Nat  BY <6>1, SMT
            <7>7. al \in QDom(x, recs)  BY <7>5, <7>6, <1>qdomchar
            <7> QED BY <7>7, <4>b
          <6> QED BY <6>1
        <5>1. HasDepth(al, x, 0)  BY <3>b, <5>d0
        <5>2. SelfL0(al, x, recs)  BY <5>1, <1>x0equiv
        <5> QED BY <5>2 DEF MQDomain
      <4> QED BY <4>a, <4>b
    <3> QED BY <3>a, <3>b
  <2> QED BY <1>dommx, <2>sub, <2>sup
\* ------------------------------------------------------------------ per-al
<1>main. \A al \in DOMAIN mqA :
       /\ mqA[al] \in Nat
       /\ \E y \in Tran(x) :
            B(y) = B(x) /\ HasDepth(al, y, mqA[al])
       /\ \A y \in Tran(x) : \A d \in Nat :
            (B(y) = B(x) /\ HasDepth(al, y, d)) => d <= mqA[al]
       /\ pqA[al]
            = {y \in Tran(x) :
                 B(y) = B(x) /\ HasDepth(al, y, mqA[al])}
  <2> SUFFICES ASSUME NEW al \in DOMAIN mqA
      PROVE /\ mqA[al] \in Nat
            /\ \E y \in Tran(x) :
                 B(y) = B(x) /\ HasDepth(al, y, mqA[al])
            /\ \A y \in Tran(x) : \A d \in Nat :
                 (B(y) = B(x) /\ HasDepth(al, y, d))
                   => d <= mqA[al]
            /\ pqA[al]
                 = {y \in Tran(x) :
                      B(y) = B(x) /\ HasDepth(al, y, mqA[al])}
    OBVIOUS
  <2>alM. al \in MQDomain(x, recs)  BY <1>dommx
  <2>alL. al \in Learners  BY <2>alM DEF MQDomain, QDom
  <2>appm. mqA[al]
             = IF al \in QDom(x, recs)
                 THEN IF Bump(al, x, recs)
                        THEN RefFrontier(al, x, recs) + 1
                        ELSE RefFrontier(al, x, recs)
                 ELSE 0
    BY <2>alM DEF MaxQDepthAssemble
  <2>appp. pqA[al]
             = IF al \in QDom(x, recs)
                 THEN IF Bump(al, x, recs)
                        THEN {x}
                        ELSE RefPending(al, x, recs)
                               \cup (IF SelfAtFrontier(al, x, recs)
                                       THEN {x} ELSE {})
                 ELSE {x}
    BY <2>alM DEF PendingQdAssemble
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
      <4>2. PICK p \in R : rc = Memo(p) /\ B(p) = B(x)  BY <4>1, <1>sbpick
      <4>3. al \in DOMAIN MemoMaxQDepth(p)  BY <4>1, <4>2, <1>idp
      <4>4. v = MemoMaxQDepth(p)[al]  BY <4>1, <4>2, <1>idp DEF QDepthCand
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
    <3>pcand. \A p \in R : (B(p) = B(x) /\ al \in DOMAIN MemoMaxQDepth(p)) =>
                MemoMaxQDepth(p)[al] \in QDepthCands(al, x, recs)
      <4> SUFFICES ASSUME NEW p \in R, B(p) = B(x),
                          al \in DOMAIN MemoMaxQDepth(p)
          PROVE MemoMaxQDepth(p)[al] \in QDepthCands(al, x, recs)
        OBVIOUS
      <4>1. Memo(p) \in SBRefs(x, recs)  BY <1>sbref
      <4>2. al \in DOMAIN Memo(p).maxqdepth  BY <1>idp
      <4>3. Memo(p) \in {y \in SBRefs(x, recs) : al \in DOMAIN y.maxqdepth}
        BY <4>1, <4>2
      <4>4. QDepthCand(al, Memo(p)) = MemoMaxQDepth(p)[al]
        BY <1>idp DEF QDepthCand
      <4> QED BY <4>3, <4>4 DEF QDepthCands
    <3>ub. \A y \in TranExclusive(x) : \A d \in Nat :
             (B(y) = B(x) /\ HasDepth(al, y, d))
               => d <= RefFrontier(al, x, recs)
      <4> SUFFICES ASSUME NEW y \in TranExclusive(x), NEW d \in Nat,
                          B(y) = B(x), HasDepth(al, y, d)
          PROVE d <= RefFrontier(al, x, recs)
        OBVIOUS
      <4>p. PICK p \in R : B(p) = B(x) /\ y \in Tran(p)  BY <1>same
      <4>dom. al \in DOMAIN MemoMaxQDepth(p)
        <5>1. al \in {a2 \in Learners :
                        \E yy \in Tran(p) :
                          B(yy) = B(p) /\ \E dd \in Nat : HasDepth(a2, yy, dd)}
          BY <4>p, <2>alL
        <5> QED BY <5>1, <4>p, <1>ih DEF MaxQDepthInvariant
      <4>max. d <= MemoMaxQDepth(p)[al]
        BY <4>p, <4>dom, <1>ih DEF MaxQDepthInvariant
      <4>c. MemoMaxQDepth(p)[al] \in QDepthCands(al, x, recs)
        BY <4>p, <4>dom, <3>pcand
      <4>le. MemoMaxQDepth(p)[al] <= RefFrontier(al, x, recs)
        BY <4>c, <3>D0
      <4>nat. MemoMaxQDepth(p)[al] \in Nat  BY <4>c, <3>cnat
      <4> QED BY <4>max, <4>le, <4>nat, <3>D0nat, SMT
    <3>att0. \E y \in TranExclusive(x) :
               B(y) = B(x) /\ HasDepth(al, y, RefFrontier(al, x, recs))
      <4>1. PICK rc \in {y \in SBRefs(x, recs) : al \in DOMAIN y.maxqdepth} :
              RefFrontier(al, x, recs) = QDepthCand(al, rc)
        BY <3>D0 DEF QDepthCands
      <4>2. PICK p \in R : rc = Memo(p) /\ B(p) = B(x)  BY <4>1, <1>sbpick
      <4>3. al \in DOMAIN MemoMaxQDepth(p)  BY <4>1, <4>2, <1>idp
      <4>4. RefFrontier(al, x, recs) = MemoMaxQDepth(p)[al]
        BY <4>1, <4>2, <1>idp DEF QDepthCand
      <4>5. \E y \in Tran(p) :
              B(y) = B(p) /\ HasDepth(al, y, MemoMaxQDepth(p)[al])
        BY <4>2, <4>3, <1>ih DEF MaxQDepthInvariant
      <4>6. PICK y \in Tran(p) :
              B(y) = B(p) /\ HasDepth(al, y, MemoMaxQDepth(p)[al])
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
        <5>2. PICK p \in R : rc = Memo(p) /\ B(p) = B(x)  BY <5>1, <1>sbpick
        <5>3. al \in DOMAIN MemoMaxQDepth(p)
                /\ MemoMaxQDepth(p)[al] = RefFrontier(al, x, recs)
          BY <5>1, <5>2, <1>idp
        <5>4. y \in MemoPendingQd(p)[al]
          BY <5>1, <5>2, <1>idp DEF RefPendingPart
        <5>5. MemoPendingQd(p)[al]
                = {yy \in Tran(p) :
                     B(yy) = B(p) /\ HasDepth(al, yy, MemoMaxQDepth(p)[al])}
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
        <5>dom. al \in DOMAIN MemoMaxQDepth(p)
          <6>1. al \in {a2 \in Learners :
                          \E yy \in Tran(p) :
                            B(yy) = B(p) /\ \E dd \in Nat : HasDepth(a2, yy, dd)}
            BY <5>p, <2>alL, <3>D0nat
          <6> QED BY <6>1, <5>p, <1>ih DEF MaxQDepthInvariant
        <5>ge. RefFrontier(al, x, recs) <= MemoMaxQDepth(p)[al]
          BY <5>p, <5>dom, <3>D0nat, <1>ih DEF MaxQDepthInvariant
        <5>le. MemoMaxQDepth(p)[al] <= RefFrontier(al, x, recs)
          <6>1. MemoMaxQDepth(p)[al] \in QDepthCands(al, x, recs)
            BY <5>p, <5>dom, <3>pcand
          <6> QED BY <6>1, <3>D0
        <5>nat. MemoMaxQDepth(p)[al] \in Nat
          BY <5>p, <5>dom, <1>ih DEF MaxQDepthInvariant
        <5>eq. MemoMaxQDepth(p)[al] = RefFrontier(al, x, recs)
          BY <5>ge, <5>le, <5>nat, <3>D0nat, SMT
        <5>mem. y \in MemoPendingQd(p)[al]
          <6>1. MemoPendingQd(p)[al]
                  = {yy \in Tran(p) :
                       B(yy) = B(p) /\ HasDepth(al, yy, MemoMaxQDepth(p)[al])}
            BY <5>p, <5>dom, <1>ih DEF MaxQDepthInvariant
          <6> QED BY <6>1, <5>p, <5>eq
        <5>flt. Memo(p) \in {z \in SBRefs(x, recs) :
                                 /\ al \in DOMAIN z.maxqdepth
                                 /\ z.maxqdepth[al] = RefFrontier(al, x, recs)}
          <6>1. Memo(p) \in SBRefs(x, recs)  BY <5>p, <1>sbref
          <6> QED BY <6>1, <5>dom, <5>eq, <1>idp
        <5>part. y \in RefPendingPart(al, Memo(p))
          BY <5>mem, <1>idp DEF RefPendingPart
        <5> QED BY <5>flt, <5>part DEF RefPending
      <4> QED BY <4>sub, <4>sup
    <3>qdx. Qd(al, x, RefFrontier(al, x, recs) + 1) = RefPending(al, x, recs)
      <4>ar. /\ RefFrontier(al, x, recs) + 1 \in Nat
             /\ RefFrontier(al, x, recs) + 1 > 0
             /\ (RefFrontier(al, x, recs) + 1) - 1 = RefFrontier(al, x, recs)
        BY <3>D0nat, SMT
      <4>sub. Qd(al, x, RefFrontier(al, x, recs) + 1)
                \subseteq RefPending(al, x, recs)
        <5> SUFFICES ASSUME NEW z \in Qd(al, x, RefFrontier(al, x, recs) + 1)
            PROVE z \in RefPending(al, x, recs)  OBVIOUS
        <5>1. z \in TranExclusive(x) /\ B(x) = B(z)
                /\ HasDepth(al, z, (RefFrontier(al, x, recs) + 1) - 1)
          BY DEF Qd
        <5>2. HasDepth(al, z, RefFrontier(al, x, recs))  BY <5>1, <4>ar
        <5> QED BY <5>1, <5>2, <3>P0
      <4>sup. RefPending(al, x, recs)
                \subseteq Qd(al, x, RefFrontier(al, x, recs) + 1)
        <5> SUFFICES ASSUME NEW z \in RefPending(al, x, recs)
            PROVE z \in Qd(al, x, RefFrontier(al, x, recs) + 1)  OBVIOUS
        <5>1. z \in TranExclusive(x) /\ B(z) = B(x)
                /\ HasDepth(al, z, RefFrontier(al, x, recs))
          BY <3>P0
        <5>2. HasDepth(al, z, (RefFrontier(al, x, recs) + 1) - 1)
          BY <5>1, <4>ar
        <5> QED BY <5>1, <5>2, <4>ar DEF Qd
      <4> QED BY <4>sub, <4>sup
    <3>hdx1. \A dd \in Nat : dd >= 1 => (HasDepth(al, x, dd) =
               (/\ Sig(x) \in Acceptors
                /\ SigS(Qd(al, x, dd)) \in Quorums(al)))
      <4> SUFFICES ASSUME NEW dd \in Nat, dd >= 1
          PROVE HasDepth(al, x, dd) =
                  (/\ Sig(x) \in Acceptors
                   /\ SigS(Qd(al, x, dd)) \in Quorums(al))
        OBVIOUS
      <4>1. HasDepth(al, x, dd) =
              (/\ Sig(x) \in Acceptors
               /\ IF dd = 0 THEN (IsOneB(x) /\ Fresh(al, x))
                            ELSE SigS(Qd(al, x, dd)) \in Quorums(al))
        BY <2>alL, <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDef
      <4> QED BY <4>1, SMT
    <3>AB. CASE Bump(al, x, recs)
      <4>fr. mqA[al] = RefFrontier(al, x, recs) + 1
        BY <2>appm, <2>A, <3>AB
      <4>pd. pqA[al] = {x}  BY <2>appp, <2>A, <3>AB
      <4>ar. RefFrontier(al, x, recs) + 1 \in Nat
               /\ RefFrontier(al, x, recs) + 1 >= 1
        BY <3>D0nat, SMT
      <4>xatt. HasDepth(al, x, RefFrontier(al, x, recs) + 1)
        <5>1. Sig(x) \in Acceptors
                /\ SigS(RefPending(al, x, recs)) \in Quorums(al)
          BY <3>AB DEF Bump
        <5>2. SigS(Qd(al, x, RefFrontier(al, x, recs) + 1)) \in Quorums(al)
          BY <5>1, <3>qdx
        <5> QED BY <5>1, <5>2, <4>ar, <3>hdx1
      <4>c1. mqA[al] \in Nat  BY <4>fr, <4>ar
      <4>c2. \E y \in Tran(x) :
               B(y) = B(x) /\ HasDepth(al, y, mqA[al])
        <5>1. x \in Tran(x)  BY DEF Tran
        <5> QED BY <5>1, <4>xatt, <4>fr
      <4>c3. \A y \in Tran(x) : \A d \in Nat :
               (B(y) = B(x) /\ HasDepth(al, y, d))
                 => d <= mqA[al]
        <5> SUFFICES ASSUME NEW y \in Tran(x), NEW d \in Nat,
                            B(y) = B(x), HasDepth(al, y, d)
            PROVE d <= mqA[al]
          OBVIOUS
        <5>a. CASE y # x
          <6>1. y \in TranExclusive(x)  BY <5>a DEF TranExclusive
          <6>2. d <= RefFrontier(al, x, recs)  BY <6>1, <3>ub
          <6> QED BY <6>2, <4>fr, <3>D0nat, SMT
        <5>b. CASE y = x
          <6>a. CASE d = 0
            <7> QED BY <6>a, <4>fr, <3>D0nat, SMT
          <6>b. CASE d # 0
            <7>1. SigS(Qd(al, x, d)) \in Quorums(al)
              BY <5>b, <6>b, <3>hdx1, SMT
            <7>2. Qd(al, x, d) # {}
              <8>1. SigS(Qd(al, x, d)) # {}  BY <7>1, <2>alL, QuorumsHaveMembers
              <8> QED BY <8>1 DEF SigS
            <7>3. PICK z \in Qd(al, x, d) : TRUE  BY <7>2
            <7>4. z \in TranExclusive(x) /\ B(x) = B(z)
                    /\ HasDepth(al, z, d - 1)
              BY <7>3 DEF Qd
            <7>5. d - 1 \in Nat  BY <6>b, SMT
            <7>6. d - 1 <= RefFrontier(al, x, recs)  BY <7>4, <7>5, <3>ub
            <7> QED BY <7>6, <4>fr, <7>5, <3>D0nat, SMT
          <6> QED BY <6>a, <6>b
        <5> QED BY <5>a, <5>b
      <4>c4. pqA[al]
               = {y \in Tran(x) :
                    B(y) = B(x) /\ HasDepth(al, y, mqA[al])}
        <5>eq. {y \in Tran(x) :
                  B(y) = B(x)
                  /\ HasDepth(al, y, RefFrontier(al, x, recs) + 1)} = {x}
          <6>sub. \A y \in Tran(x) :
                    (B(y) = B(x)
                     /\ HasDepth(al, y, RefFrontier(al, x, recs) + 1))
                      => y = x
            <7> SUFFICES ASSUME NEW y \in Tran(x), B(y) = B(x),
                                HasDepth(al, y, RefFrontier(al, x, recs) + 1),
                                y # x
                PROVE FALSE
              OBVIOUS
            <7>1. y \in TranExclusive(x)  BY DEF TranExclusive
            <7>2. RefFrontier(al, x, recs) + 1 <= RefFrontier(al, x, recs)
              BY <7>1, <3>ub, <3>D0nat, SMT
            <7> QED BY <7>2, <3>D0nat, SMT
          <6>x. x \in Tran(x)  BY DEF Tran
          <6> QED BY <6>sub, <6>x, <4>xatt
        <5> QED BY <5>eq, <4>pd, <4>fr
      <4> QED BY <4>c1, <4>c2, <4>c3, <4>c4
    <3>NB. CASE ~Bump(al, x, recs)
      <4>fr. mqA[al] = RefFrontier(al, x, recs)
        BY <2>appm, <2>A, <3>NB
      <4>pd. pqA[al]
               = RefPending(al, x, recs)
                   \cup (IF SelfAtFrontier(al, x, recs) THEN {x} ELSE {})
        BY <2>appp, <2>A, <3>NB
      <4>c1. mqA[al] \in Nat  BY <4>fr, <3>D0nat
      <4>c2. \E y \in Tran(x) :
               B(y) = B(x) /\ HasDepth(al, y, mqA[al])
        <5>1. PICK y \in TranExclusive(x) :
                B(y) = B(x) /\ HasDepth(al, y, RefFrontier(al, x, recs))
          BY <3>att0
        <5>2. y \in Tran(x)  BY DEF TranExclusive
        <5> QED BY <5>1, <5>2, <4>fr
      <4>c3. \A y \in Tran(x) : \A d \in Nat :
               (B(y) = B(x) /\ HasDepth(al, y, d))
                 => d <= mqA[al]
        <5> SUFFICES ASSUME NEW y \in Tran(x), NEW d \in Nat,
                            B(y) = B(x), HasDepth(al, y, d)
            PROVE d <= mqA[al]
          OBVIOUS
        <5>a. CASE y # x
          <6>1. y \in TranExclusive(x)  BY <5>a DEF TranExclusive
          <6> QED BY <6>1, <3>ub, <4>fr
        <5>b. CASE y = x
          <6>a. CASE d = 0
            <7> QED BY <6>a, <4>fr, <3>D0nat, SMT
          <6>b. CASE d # 0
            <7>1. SigS(Qd(al, x, d)) \in Quorums(al) /\ Sig(x) \in Acceptors
              BY <5>b, <6>b, <3>hdx1, SMT
            <7>2. Qd(al, x, d) # {}
              <8>1. SigS(Qd(al, x, d)) # {}  BY <7>1, <2>alL, QuorumsHaveMembers
              <8> QED BY <8>1 DEF SigS
            <7>3. PICK z \in Qd(al, x, d) : TRUE  BY <7>2
            <7>4. z \in TranExclusive(x) /\ B(x) = B(z)
                    /\ HasDepth(al, z, d - 1)
              BY <7>3 DEF Qd
            <7>5. d - 1 \in Nat  BY <6>b, SMT
            <7>6. d - 1 <= RefFrontier(al, x, recs)  BY <7>4, <7>5, <3>ub
            <7>ne. d # RefFrontier(al, x, recs) + 1
              <8>1. CASE d = RefFrontier(al, x, recs) + 1
                <9>1. SigS(Qd(al, x, RefFrontier(al, x, recs) + 1))
                        \in Quorums(al)
                  BY <7>1, <8>1
                <9>2. SigS(RefPending(al, x, recs)) \in Quorums(al)
                  BY <9>1, <3>qdx
                <9>3. Bump(al, x, recs)  BY <9>2, <7>1 DEF Bump
                <9> QED BY <9>3, <3>NB
              <8> QED BY <8>1
            <7> QED BY <7>6, <7>ne, <7>5, <3>D0nat, <4>fr, SMT
          <6> QED BY <6>a, <6>b
        <5> QED BY <5>a, <5>b
      <4>saf. SelfAtFrontier(al, x, recs)
                <=> HasDepth(al, x, RefFrontier(al, x, recs))
        <5>a. CASE RefFrontier(al, x, recs) >= 1
          <6>1. SelfAtFrontier(al, x, recs) <=> Sig(x) \in Acceptors
            BY <5>a DEF SelfAtFrontier
          <6>fwd. Sig(x) \in Acceptors
                    => HasDepth(al, x, RefFrontier(al, x, recs))
            <7>1. CASE Sig(x) \in Acceptors
              <8>1. PICK y \in TranExclusive(x) :
                      B(y) = B(x)
                      /\ HasDepth(al, y, RefFrontier(al, x, recs))
                BY <3>att0
              <8> QED BY <7>1, <8>1, <5>a, <3>D0nat, <2>alL,
                        <1>tok, <1>tt, <1>tf, <1>ta, AttesterInherit
            <7> QED BY <7>1
          <6>bwd. HasDepth(al, x, RefFrontier(al, x, recs))
                    => Sig(x) \in Acceptors
            <7>1. HasDepth(al, x, RefFrontier(al, x, recs)) =
                    (/\ Sig(x) \in Acceptors
                     /\ IF RefFrontier(al, x, recs) = 0
                          THEN (IsOneB(x) /\ Fresh(al, x))
                          ELSE SigS(Qd(al, x, RefFrontier(al, x, recs)))
                                 \in Quorums(al))
              BY <3>D0nat, <2>alL, <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDef
            <7> QED BY <7>1
          <6> QED BY <6>1, <6>fwd, <6>bwd
        <5>b. CASE ~(RefFrontier(al, x, recs) >= 1)
          <6>0. RefFrontier(al, x, recs) = 0  BY <5>b, <3>D0nat, SMT
          <6>1. SelfAtFrontier(al, x, recs) <=> SelfL0(al, x, recs)
            BY <5>b DEF SelfAtFrontier
          <6>2. SelfL0(al, x, recs) <=> HasDepth(al, x, 0)
            BY <2>alL, <1>x0equiv
          <6> QED BY <6>1, <6>2, <6>0
        <5> QED BY <5>a, <5>b
      <4>c4. pqA[al]
               = {y \in Tran(x) :
                    B(y) = B(x) /\ HasDepth(al, y, mqA[al])}
        <5>sub. \A y \in Tran(x) :
                  (B(y) = B(x) /\ HasDepth(al, y, RefFrontier(al, x, recs)))
                    => y \in pqA[al]
          <6> SUFFICES ASSUME NEW y \in Tran(x), B(y) = B(x),
                              HasDepth(al, y, RefFrontier(al, x, recs))
              PROVE y \in pqA[al]
            OBVIOUS
          <6>a. CASE y = x
            <7>1. SelfAtFrontier(al, x, recs)  BY <6>a, <4>saf
            <7> QED BY <7>1, <6>a, <4>pd
          <6>b. CASE y # x
            <7>1. y \in TranExclusive(x)  BY <6>b DEF TranExclusive
            <7>2. y \in RefPending(al, x, recs)  BY <7>1, <3>P0
            <7> QED BY <7>2, <4>pd
          <6> QED BY <6>a, <6>b
        <5>sup. \A y \in pqA[al] :
                  y \in Tran(x) /\ B(y) = B(x)
                    /\ HasDepth(al, y, RefFrontier(al, x, recs))
          <6> SUFFICES ASSUME NEW y \in pqA[al]
              PROVE y \in Tran(x) /\ B(y) = B(x)
                      /\ HasDepth(al, y, RefFrontier(al, x, recs))
            OBVIOUS
          <6>a. CASE y \in RefPending(al, x, recs)
            <7>1. y \in TranExclusive(x) /\ B(y) = B(x)
                    /\ HasDepth(al, y, RefFrontier(al, x, recs))
              BY <6>a, <3>P0
            <7> QED BY <7>1 DEF TranExclusive
          <6>b. CASE y \notin RefPending(al, x, recs)
            <7>1. y = x /\ SelfAtFrontier(al, x, recs)  BY <6>b, <4>pd
            <7>2. HasDepth(al, x, RefFrontier(al, x, recs))
              BY <7>1, <4>saf
            <7>3. x \in Tran(x)  BY DEF Tran
            <7> QED BY <7>1, <7>2, <7>3
          <6> QED BY <6>a, <6>b
        <5> QED BY <5>sub, <5>sup, <4>fr
      <4> QED BY <4>c1, <4>c2, <4>c3, <4>c4
    <3> QED BY <3>AB, <3>NB
  <2>B. CASE al \notin QDom(x, recs)
    <3>self. SelfL0(al, x, recs)  BY <2>alM, <2>B DEF MQDomain
    <3>fr. mqA[al] = 0  BY <2>appm, <2>B
    <3>pd. pqA[al] = {x}  BY <2>appp, <2>B
    <3>x0. HasDepth(al, x, 0)  BY <3>self, <2>alL, <1>x0equiv
    <3>noTE. \A y \in TranExclusive(x) :
               ~(B(y) = B(x) /\ \E d \in Nat : HasDepth(al, y, d))
      BY <2>B, <2>alL, <1>qdomchar
    <3>c1. mqA[al] \in Nat  BY <3>fr
    <3>c2. \E y \in Tran(x) :
             B(y) = B(x) /\ HasDepth(al, y, mqA[al])
      <4>1. x \in Tran(x)  BY DEF Tran
      <4> QED BY <4>1, <3>x0, <3>fr
    <3>c3. \A y \in Tran(x) : \A d \in Nat :
             (B(y) = B(x) /\ HasDepth(al, y, d))
               => d <= mqA[al]
      <4> SUFFICES ASSUME NEW y \in Tran(x), NEW d \in Nat,
                          B(y) = B(x), HasDepth(al, y, d)
          PROVE d <= mqA[al]
        OBVIOUS
      <4>a. CASE y # x
        <5>1. y \in TranExclusive(x)  BY <4>a DEF TranExclusive
        <5> QED BY <5>1, <3>noTE
      <4>b. CASE y = x
        <5>a. CASE d = 0
          <6> QED BY <5>a, <3>fr
        <5>b. CASE d # 0
          <6>1. HasDepth(al, x, d) =
                  (/\ Sig(x) \in Acceptors
                   /\ IF d = 0 THEN (IsOneB(x) /\ Fresh(al, x))
                               ELSE SigS(Qd(al, x, d)) \in Quorums(al))
            BY <2>alL, <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDef
          <6>2. SigS(Qd(al, x, d)) \in Quorums(al)  BY <6>1, <4>b, <5>b
          <6>3. Qd(al, x, d) # {}
            <7>1. SigS(Qd(al, x, d)) # {}  BY <6>2, <2>alL, QuorumsHaveMembers
            <7> QED BY <7>1 DEF SigS
          <6>4. PICK z \in Qd(al, x, d) : TRUE  BY <6>3
          <6>5. z \in TranExclusive(x) /\ B(x) = B(z)
                  /\ HasDepth(al, z, d - 1)
            BY <6>4 DEF Qd
          <6>6. d - 1 \in Nat  BY <5>b, SMT
          <6> QED BY <6>5, <6>6, <3>noTE
        <5> QED BY <5>a, <5>b
      <4> QED BY <4>a, <4>b
    <3>c4. pqA[al]
             = {y \in Tran(x) :
                  B(y) = B(x) /\ HasDepth(al, y, mqA[al])}
      <4>eq. {y \in Tran(x) : B(y) = B(x) /\ HasDepth(al, y, 0)} = {x}
        <5>sub. \A y \in Tran(x) :
                  (B(y) = B(x) /\ HasDepth(al, y, 0)) => y = x
          <6> SUFFICES ASSUME NEW y \in Tran(x), B(y) = B(x),
                              HasDepth(al, y, 0), y # x
              PROVE FALSE
            OBVIOUS
          <6>1. y \in TranExclusive(x)  BY DEF TranExclusive
          <6> QED BY <6>1, <3>noTE
        <5>x. x \in Tran(x)  BY DEF Tran
        <5> QED BY <5>sub, <5>x, <3>x0
      <4> QED BY <4>eq, <3>pd, <3>fr
    <3> QED BY <3>c1, <3>c2, <3>c3, <3>c4
  <2> QED BY <2>A, <2>B
<1> QED BY <1>dom, <1>dommx, <1>dompd, <1>main DEF MaxQDepthCorrect
====================================================================
