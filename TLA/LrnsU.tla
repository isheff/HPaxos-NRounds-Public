--------------------------------- MODULE LrnsU ---------------------------------
\* Plan step (e) toward CWellFormedRec: the memo-based WFRLrns check on the
\* candidate's priors decides the candidate's own depth-1 attestations.
\* Adapted from LrnsStep with x := cand and TranExclusive(x) := U (the union
\* of the priors' closures, = CTranExcl(cand) by CBuiltTran).  The members of
\* U ARE Messages, so their HasDepth/B facts stay interface-side (via the
\* Resolve lemmas); only the candidate's own depth-1 reading needs the
\* concrete unfold, supplied by CQdCompute at the CMC record: its level-1 Qd
\* set is exactly the level-0 same-ballot attesters of U.  Frontier >= 1:
\* step the frontier attester down to level 1 (HasDepthDownward) and widen
\* its quorum (QuorumUpward).  Frontier 0: the pending set IS the level-0
\* attester set (Bump).  No frontier: no attesters, and quorums are never
\* empty.
EXTENDS WellFormedRecDef, BalU, CBuiltInCMC, CQdCompute, CHasDepthResolve,
        CSigSResolve, MaxQDepthInv, MemoRec, HasDepthDef, HasDepthDownward,
        QuorumUpward, QuorumsHaveMembers, TranSubMessages, BBallot
LOCAL INSTANCE TLAPS

LEMMA LrnsU ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         MessageInterface = CMI,
         NEW sdr \in CSenders, NEW pl \in CPayload,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr),
         pl \in CProposal \/ pr # {}
  PROVE LET cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
            r    == {Memo(p) : p \in pr}
        IN  /\ WFRLrns(sdr, pl, r) \subseteq Learners
            /\ \A alpha \in Learners :
                 CHasDepth(alpha, cand, 1) <=> alpha \in WFRLrns(sdr, pl, r)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
<1> DEFINE r    == {Memo(p) : p \in pr}
<1> DEFINE U    == UNION {Tran(p) : p \in pr}
<1>msub. pr \subseteq Messages  BY CFields
<1>ueqp. \A p \in pr : Tran(p) = CTran(p)  BY CTranResolve
<1>ueq. U = UNION {CTran(p) : p \in pr}
  <2>sub. U \subseteq UNION {CTran(p) : p \in pr}
    <3> SUFFICES ASSUME NEW z \in U
        PROVE z \in UNION {CTran(p) : p \in pr}  OBVIOUS
    <3>1. PICK p \in pr : z \in Tran(p)  OBVIOUS
    <3> QED BY <3>1, <1>ueqp
  <2>sup. UNION {CTran(p) : p \in pr} \subseteq U
    <3> SUFFICES ASSUME NEW z \in UNION {CTran(p) : p \in pr}
        PROVE z \in U  OBVIOUS
    <3>1. PICK p \in pr : z \in CTran(p)  OBVIOUS
    <3> QED BY <3>1, <1>ueqp
  <2> QED BY <2>sub, <2>sup
<1>ctex. CTranExcl(cand) = U
  <2>1. CTranExcl(cand) = UNION {CTran(p) : p \in pr}  BY CBuiltTran
  <2> QED BY <2>1, <1>ueq
<1>uMc. U \subseteq CMessages
  <2>1. UNION {CTran(p) : p \in pr} \subseteq CMessages
    BY CUnionTranFiniteClosed
  <2> QED BY <2>1, <1>ueq
<1>uM. U \subseteq Messages  BY <1>uMc, CFields
<1>ufin. IsFiniteSet(U)
  <2>1. IsFiniteSet(UNION {CTran(p) : p \in pr})  BY CUnionTranFiniteClosed
  <2> QED BY <2>1, <1>ueq
<1>ucl. \A z \in U : Tran(z) \subseteq U
  <2> SUFFICES ASSUME NEW z \in U PROVE Tran(z) \subseteq U  OBVIOUS
  <2>1. PICK p \in pr : z \in Tran(p)  OBVIOUS
  <2>2. Tran(z) \subseteq Tran(p)  BY <2>1, <1>tt, <1>msub DEF TranTrans
  <2> QED BY <2>1, <2>2
<1>pU. \A p \in pr : p \in U
  <2> SUFFICES ASSUME NEW p \in pr PROVE p \in U  OBVIOUS
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1
<1>bal. /\ CB(cand) = WFRBal(pl, r)
        /\ CB(cand) \in Nat
        /\ \A p \in pr : CB(p) <= CB(cand)
  BY <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalU
<1>ble. \A p \in pr : B(p) <= CB(cand) /\ B(p) \in Nat
  <2> SUFFICES ASSUME NEW p \in pr
      PROVE B(p) <= CB(cand) /\ B(p) \in Nat  OBVIOUS
  <2>1. B(p) = CB(p)  BY CBResolve
  <2>2. p \in Messages  BY <1>msub
  <2>3. B(p) \in Ballots  BY <2>2, <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>1, <2>3, <1>bal DEF Ballots
<1>unat. \A y \in U : B(y) \in Nat
  <2> SUFFICES ASSUME NEW y \in U PROVE B(y) \in Nat  OBVIOUS
  <2>1. y \in Messages  BY <1>uM
  <2>2. B(y) \in Ballots  BY <2>1, <1>tok, <1>tf, <1>anp, BBallot
  <2> QED BY <2>2 DEF Ballots
<1>idp. \A p \in pr : /\ Memo(p).id = p
                      /\ Memo(p).bal = B(p)
                      /\ Memo(p).maxqdepth = MemoMaxQDepth(p)
                      /\ Memo(p).pendingqd = MemoPendingQd(p)
  <2> SUFFICES ASSUME NEW p \in pr
      PROVE /\ Memo(p).id = p
            /\ Memo(p).bal = B(p)
            /\ Memo(p).maxqdepth = MemoMaxQDepth(p)
            /\ Memo(p).pendingqd = MemoPendingQd(p)
    OBVIOUS
  <2>1. p \in Messages  BY <1>msub
  <2>2. Memo(p) = MemoR(p, {Memo(q) : q \in Refs(p)})
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, MemoRec
  <2>3. MemoBal(p) = B(p)
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
  <2> QED BY <2>2, <2>3
    DEF MemoR, MemoBal, MemoMaxQDepth, MemoPendingQd
<1>ihmq. \A p \in pr : MaxQDepthInvariant(p)
  BY <1>msub, MaxQDepthInv
<1>sbref. \A p \in pr : (Memo(p) \in WFRSBRefs(pl, r)) <=> (B(p) = CB(cand))
  BY <1>idp, <1>bal DEF WFRSBRefs
<1>sbpick. \A rc \in WFRSBRefs(pl, r) :
             \E p \in pr : rc = Memo(p) /\ B(p) = CB(cand)
  <2> SUFFICES ASSUME NEW rc \in WFRSBRefs(pl, r)
      PROVE \E p \in pr : rc = Memo(p) /\ B(p) = CB(cand)
    OBVIOUS
  <2>1. rc \in r /\ rc.bal = WFRBal(pl, r)  BY DEF WFRSBRefs
  <2>2. PICK p \in pr : rc = Memo(p)  BY <2>1
  <2> QED BY <2>1, <2>2, <1>idp, <1>bal
<1>same. \A y \in U :
           B(y) = CB(cand) => \E p \in pr : B(p) = CB(cand) /\ y \in Tran(p)
  <2> SUFFICES ASSUME NEW y \in U, B(y) = CB(cand)
      PROVE \E p \in pr : B(p) = CB(cand) /\ y \in Tran(p)
    OBVIOUS
  <2>p. PICK p \in pr : y \in Tran(p)  OBVIOUS
  <2>pM. p \in Messages  BY <1>msub
  <2>1. B(y) <= B(p)
    BY <2>p, <2>pM, <1>tok, <1>tt, <1>tf, <1>anp, BMonotone
  <2>2. B(p) <= CB(cand) /\ B(p) \in Nat  BY <1>ble
  <2>3. B(y) \in Nat  BY <1>unat
  <2>4. B(p) = CB(cand)  BY <2>1, <2>2, <2>3, <1>bal, SMT
  <2> QED BY <2>p, <2>4
<1>qdomchar. \A al \in Learners :
    al \in WFRQDom(pl, r)
    <=> (\E y \in U : B(y) = CB(cand) /\ \E d \in Nat : HasDepth(al, y, d))
  <2> SUFFICES ASSUME NEW al \in Learners
      PROVE al \in WFRQDom(pl, r)
              <=> (\E y \in U :
                     B(y) = CB(cand) /\ \E d \in Nat : HasDepth(al, y, d))
    OBVIOUS
  <2>fwd. al \in WFRQDom(pl, r) =>
            \E y \in U : B(y) = CB(cand) /\ \E d \in Nat : HasDepth(al, y, d)
    <3>1. CASE al \in WFRQDom(pl, r)
      <4>1. PICK rc \in WFRSBRefs(pl, r) : al \in DOMAIN rc.maxqdepth
        BY <3>1 DEF WFRQDom
      <4>2. PICK p \in pr : rc = Memo(p) /\ B(p) = CB(cand)
        BY <4>1, <1>sbpick
      <4>3. al \in DOMAIN MemoMaxQDepth(p)  BY <4>1, <4>2, <1>idp
      <4>4. \E y \in Tran(p) : B(y) = B(p) /\ \E d \in Nat : HasDepth(al, y, d)
        BY <4>2, <4>3, <1>ihmq DEF MaxQDepthInvariant
      <4>5. PICK y \in Tran(p) :
              B(y) = B(p) /\ \E d \in Nat : HasDepth(al, y, d)
        BY <4>4
      <4>6. y \in U  BY <4>5
      <4> QED BY <4>2, <4>5, <4>6
    <3> QED BY <3>1
  <2>bwd. (\E y \in U : B(y) = CB(cand) /\ \E d \in Nat : HasDepth(al, y, d))
          => al \in WFRQDom(pl, r)
    <3>1. CASE \E y \in U :
                 B(y) = CB(cand) /\ \E d \in Nat : HasDepth(al, y, d)
      <4>y. PICK y \in U :
              B(y) = CB(cand) /\ \E d \in Nat : HasDepth(al, y, d)
        BY <3>1
      <4>p. PICK p \in pr : B(p) = CB(cand) /\ y \in Tran(p)
        BY <4>y, <1>same
      <4>1. al \in {a2 \in Learners :
                      \E yy \in Tran(p) :
                        B(yy) = B(p) /\ \E d \in Nat : HasDepth(a2, yy, d)}
        BY <4>y, <4>p
      <4>2. al \in DOMAIN MemoMaxQDepth(p)
        BY <4>1, <4>p, <1>ihmq DEF MaxQDepthInvariant
      <4>3. Memo(p) \in WFRSBRefs(pl, r)  BY <4>p, <1>sbref
      <4>4. al \in DOMAIN Memo(p).maxqdepth  BY <4>2, <1>idp
      <4> QED BY <4>3, <4>4 DEF WFRQDom
    <3> QED BY <3>1
  <2> QED BY <2>fwd, <2>bwd
<1>cmc. cand \in CMC  BY CBuiltInCMC
<1>csig. CSig(cand) = sdr  BY DEF CSig
<1>iff. \A al \in Learners :
          CHasDepth(al, cand, 1) <=> al \in WFRLrns(sdr, pl, r)
  <2> SUFFICES ASSUME NEW al \in Learners
      PROVE CHasDepth(al, cand, 1) <=> al \in WFRLrns(sdr, pl, r)
    OBVIOUS
  <2> DEFINE QU1 == {z \in U : B(z) = CB(cand) /\ HasDepth(al, z, 0)}
  <2>ar. 1 \in Nat /\ 1 >= 1 /\ 1 - 1 = 0 /\ 1 # 0 /\ 0 \in Nat  BY SMT
  <2>cq. CCfl(cand).qd[<<al, 1>>] = QU1
    <3>0. CCfl(cand).qd[<<al, 1>>]
            = {z \in CTranExcl(cand) :
                 CB(z) = CB(cand) /\ CHasDepth(al, z, 1-1)}
      BY <1>cmc, <2>ar, CQdCompute
    <3>res. \A z \in U : /\ CB(z) = B(z)
                         /\ CHasDepth(al, z, 0) = HasDepth(al, z, 0)
      <4> SUFFICES ASSUME NEW z \in U
          PROVE /\ CB(z) = B(z)
                /\ CHasDepth(al, z, 0) = HasDepth(al, z, 0)
        OBVIOUS
      <4>1. z \in CMessages  BY <1>uMc
      <4>2. B(z) = CB(z)  BY <4>1, CBResolve
      <4>3. HasDepth(al, z, 0) = CHasDepth(al, z, 0)
        BY <4>1, <2>ar, CHasDepthResolve
      <4> QED BY <4>2, <4>3
    <3>sub. CCfl(cand).qd[<<al, 1>>] \subseteq QU1
      <4> SUFFICES ASSUME NEW z \in CCfl(cand).qd[<<al, 1>>]
          PROVE z \in QU1  OBVIOUS
      <4>1. z \in CTranExcl(cand) /\ CB(z) = CB(cand)
              /\ CHasDepth(al, z, 1-1)
        BY <3>0
      <4>2. z \in U  BY <4>1, <1>ctex
      <4>3. CHasDepth(al, z, 0)  BY <4>1, <2>ar
      <4>4. B(z) = CB(cand) /\ HasDepth(al, z, 0)  BY <4>1, <4>2, <4>3, <3>res
      <4> QED BY <4>2, <4>4
    <3>sup. QU1 \subseteq CCfl(cand).qd[<<al, 1>>]
      <4> SUFFICES ASSUME NEW z \in QU1
          PROVE z \in CCfl(cand).qd[<<al, 1>>]  OBVIOUS
      <4>1. z \in U /\ B(z) = CB(cand) /\ HasDepth(al, z, 0)  OBVIOUS
      <4>2. z \in CTranExcl(cand)  BY <4>1, <1>ctex
      <4>3. CB(z) = CB(cand) /\ CHasDepth(al, z, 0)  BY <4>1, <3>res
      <4>4. CHasDepth(al, z, 1-1)  BY <4>3, <2>ar
      <4> QED BY <3>0, <4>2, <4>3, <4>4
    <3> QED BY <3>sub, <3>sup
  <2>hd1. CHasDepth(al, cand, 1)
            <=> (sdr \in Acceptors /\ SigS(QU1) \in Quorums(al))
    <3>1. CHasDepth(al, cand, 1)
            = (/\ CSig(cand) \in Acceptors
               /\ CSigS(CCfl(cand).qd[<<al, 1>>]) \in Quorums(al))
      BY <2>ar DEF CHasDepth
    <3>2. QU1 \subseteq CMessages  BY <1>uMc
    <3>3. CSigS(QU1) = SigS(QU1)  BY <3>2, CSigSResolve
    <3> QED BY <3>1, <3>3, <2>cq, <1>csig
  <2>A. CASE al \in WFRQDom(pl, r)
    <3>cne. WFRQDepthCands(al, pl, r) # {}
      <4>1. PICK rc \in WFRSBRefs(pl, r) : al \in DOMAIN rc.maxqdepth
        BY <2>A DEF WFRQDom
      <4>2. rc \in {y \in WFRSBRefs(pl, r) : al \in DOMAIN y.maxqdepth}
        BY <4>1
      <4> QED BY <4>2 DEF WFRQDepthCands, QDepthCand
    <3>cnat. \A v \in WFRQDepthCands(al, pl, r) : v \in Nat
      <4> SUFFICES ASSUME NEW v \in WFRQDepthCands(al, pl, r)
          PROVE v \in Nat  OBVIOUS
      <4>1. PICK rc \in {y \in WFRSBRefs(pl, r) : al \in DOMAIN y.maxqdepth} :
              v = QDepthCand(al, rc)
        BY DEF WFRQDepthCands
      <4>2. PICK p \in pr : rc = Memo(p) /\ B(p) = CB(cand)
        BY <4>1, <1>sbpick
      <4>3. al \in DOMAIN MemoMaxQDepth(p)  BY <4>1, <4>2, <1>idp
      <4>4. v = MemoMaxQDepth(p)[al]  BY <4>1, <4>2, <1>idp DEF QDepthCand
      <4> QED BY <4>3, <4>4, <4>2, <1>ihmq DEF MaxQDepthInvariant
    <3>cfin. IsFiniteSet(WFRQDepthCands(al, pl, r))
      <4>frecs. IsFiniteSet(r)  BY FS_Image
      <4>f1. IsFiniteSet(WFRSBRefs(pl, r))
        BY <4>frecs, FS_Subset DEF WFRSBRefs
      <4>f2. IsFiniteSet({y \in WFRSBRefs(pl, r) : al \in DOMAIN y.maxqdepth})
        BY <4>f1, FS_Subset
      <4> QED BY <4>f2, FS_Image DEF WFRQDepthCands
    <3>D0. /\ WFRRefFrontier(al, pl, r) \in WFRQDepthCands(al, pl, r)
           /\ \A v \in WFRQDepthCands(al, pl, r) :
                WFRRefFrontier(al, pl, r) >= v
      BY <3>cne, <3>cnat, <3>cfin, MaxProps DEF WFRRefFrontier
    <3>D0nat. WFRRefFrontier(al, pl, r) \in Nat  BY <3>D0, <3>cnat
    <3>pcand. \A p \in pr :
                (B(p) = CB(cand) /\ al \in DOMAIN MemoMaxQDepth(p)) =>
                  MemoMaxQDepth(p)[al] \in WFRQDepthCands(al, pl, r)
      <4> SUFFICES ASSUME NEW p \in pr, B(p) = CB(cand),
                          al \in DOMAIN MemoMaxQDepth(p)
          PROVE MemoMaxQDepth(p)[al] \in WFRQDepthCands(al, pl, r)
        OBVIOUS
      <4>1. Memo(p) \in WFRSBRefs(pl, r)  BY <1>sbref
      <4>2. al \in DOMAIN Memo(p).maxqdepth  BY <1>idp
      <4>3. Memo(p)
              \in {y \in WFRSBRefs(pl, r) : al \in DOMAIN y.maxqdepth}
        BY <4>1, <4>2
      <4>4. QDepthCand(al, Memo(p)) = MemoMaxQDepth(p)[al]
        BY <1>idp DEF QDepthCand
      <4> QED BY <4>3, <4>4 DEF WFRQDepthCands
    <3>att0. \E y \in U :
               B(y) = CB(cand)
               /\ HasDepth(al, y, WFRRefFrontier(al, pl, r))
      <4>1. PICK rc \in {y \in WFRSBRefs(pl, r) : al \in DOMAIN y.maxqdepth} :
              WFRRefFrontier(al, pl, r) = QDepthCand(al, rc)
        BY <3>D0 DEF WFRQDepthCands
      <4>2. PICK p \in pr : rc = Memo(p) /\ B(p) = CB(cand)
        BY <4>1, <1>sbpick
      <4>3. al \in DOMAIN MemoMaxQDepth(p)  BY <4>1, <4>2, <1>idp
      <4>4. WFRRefFrontier(al, pl, r) = MemoMaxQDepth(p)[al]
        BY <4>1, <4>2, <1>idp DEF QDepthCand
      <4>5. \E y \in Tran(p) :
              B(y) = B(p) /\ HasDepth(al, y, MemoMaxQDepth(p)[al])
        BY <4>2, <4>3, <1>ihmq DEF MaxQDepthInvariant
      <4>6. PICK y \in Tran(p) :
              B(y) = B(p) /\ HasDepth(al, y, MemoMaxQDepth(p)[al])
        BY <4>5
      <4>7. y \in U  OBVIOUS
      <4> QED BY <4>2, <4>4, <4>6, <4>7
    <3>P0. WFRRefPending(al, pl, r)
             = {y \in U :
                  B(y) = CB(cand)
                  /\ HasDepth(al, y, WFRRefFrontier(al, pl, r))}
      <4>sub. WFRRefPending(al, pl, r) \subseteq
                {y \in U :
                   B(y) = CB(cand)
                   /\ HasDepth(al, y, WFRRefFrontier(al, pl, r))}
        <5> SUFFICES ASSUME NEW y \in WFRRefPending(al, pl, r)
            PROVE y \in {yy \in U :
                           B(yy) = CB(cand)
                           /\ HasDepth(al, yy, WFRRefFrontier(al, pl, r))}
          OBVIOUS
        <5>1. PICK rc \in {z \in WFRSBRefs(pl, r) :
                             /\ al \in DOMAIN z.maxqdepth
                             /\ z.maxqdepth[al]
                                  = WFRRefFrontier(al, pl, r)} :
                y \in RefPendingPart(al, rc)
          BY DEF WFRRefPending
        <5>2. PICK p \in pr : rc = Memo(p) /\ B(p) = CB(cand)
          BY <5>1, <1>sbpick
        <5>3. al \in DOMAIN MemoMaxQDepth(p)
                /\ MemoMaxQDepth(p)[al] = WFRRefFrontier(al, pl, r)
          BY <5>1, <5>2, <1>idp
        <5>4. y \in MemoPendingQd(p)[al]
          BY <5>1, <5>2, <1>idp DEF RefPendingPart
        <5>5. MemoPendingQd(p)[al]
                = {yy \in Tran(p) :
                     B(yy) = B(p)
                     /\ HasDepth(al, yy, MemoMaxQDepth(p)[al])}
          BY <5>2, <5>3, <1>ihmq DEF MaxQDepthInvariant
        <5>6. y \in Tran(p) /\ B(y) = B(p)
                /\ HasDepth(al, y, WFRRefFrontier(al, pl, r))
          BY <5>4, <5>5, <5>3
        <5>7. y \in U  BY <5>6
        <5> QED BY <5>2, <5>6, <5>7
      <4>sup. {y \in U :
                 B(y) = CB(cand)
                 /\ HasDepth(al, y, WFRRefFrontier(al, pl, r))}
                \subseteq WFRRefPending(al, pl, r)
        <5> SUFFICES ASSUME NEW y \in U, B(y) = CB(cand),
                            HasDepth(al, y, WFRRefFrontier(al, pl, r))
            PROVE y \in WFRRefPending(al, pl, r)
          OBVIOUS
        <5>p. PICK p \in pr : B(p) = CB(cand) /\ y \in Tran(p)  BY <1>same
        <5>dom. al \in DOMAIN MemoMaxQDepth(p)
          <6>1. al \in {a2 \in Learners :
                          \E yy \in Tran(p) :
                            B(yy) = B(p)
                            /\ \E dd \in Nat : HasDepth(a2, yy, dd)}
            BY <5>p, <3>D0nat
          <6> QED BY <6>1, <5>p, <1>ihmq DEF MaxQDepthInvariant
        <5>ge. WFRRefFrontier(al, pl, r) <= MemoMaxQDepth(p)[al]
          BY <5>p, <5>dom, <3>D0nat, <1>ihmq DEF MaxQDepthInvariant
        <5>le. MemoMaxQDepth(p)[al] <= WFRRefFrontier(al, pl, r)
          <6>1. MemoMaxQDepth(p)[al] \in WFRQDepthCands(al, pl, r)
            BY <5>p, <5>dom, <3>pcand
          <6> QED BY <6>1, <3>D0
        <5>nat. MemoMaxQDepth(p)[al] \in Nat
          BY <5>p, <5>dom, <1>ihmq DEF MaxQDepthInvariant
        <5>eq. MemoMaxQDepth(p)[al] = WFRRefFrontier(al, pl, r)
          BY <5>ge, <5>le, <5>nat, <3>D0nat, SMT
        <5>mem. y \in MemoPendingQd(p)[al]
          <6>1. MemoPendingQd(p)[al]
                  = {yy \in Tran(p) :
                       B(yy) = B(p)
                       /\ HasDepth(al, yy, MemoMaxQDepth(p)[al])}
            BY <5>p, <5>dom, <1>ihmq DEF MaxQDepthInvariant
          <6> QED BY <6>1, <5>p, <5>eq
        <5>flt. Memo(p) \in {z \in WFRSBRefs(pl, r) :
                                 /\ al \in DOMAIN z.maxqdepth
                                 /\ z.maxqdepth[al]
                                      = WFRRefFrontier(al, pl, r)}
          <6>1. Memo(p) \in WFRSBRefs(pl, r)  BY <5>p, <1>sbref
          <6> QED BY <6>1, <5>dom, <5>eq, <1>idp
        <5>part. y \in RefPendingPart(al, Memo(p))
          BY <5>mem, <1>idp DEF RefPendingPart
        <5> QED BY <5>flt, <5>part DEF WFRRefPending
      <4> QED BY <4>sub, <4>sup
    <3>mem. al \in WFRLrns(sdr, pl, r)
              <=> (IF WFRRefFrontier(al, pl, r) >= 1
                     THEN sdr \in Acceptors
                     ELSE WFRBump(al, sdr, pl, r))
      BY <2>A DEF WFRLrns
    <3>a. CASE WFRRefFrontier(al, pl, r) >= 1
      <4>fwd. sdr \in Acceptors => CHasDepth(al, cand, 1)
        <5>1. CASE sdr \in Acceptors
          <6>y. PICK y \in U :
                  B(y) = CB(cand)
                  /\ HasDepth(al, y, WFRRefFrontier(al, pl, r))
            BY <3>att0
          <6>yM. y \in Messages  BY <1>uM
          <6>d1. HasDepth(al, y, 1)
            BY <6>y, <6>yM, <3>a, <3>D0nat, <2>ar,
               <1>tok, <1>tt, <1>tf, <1>ta,
               LearnersMightAgree, ValidLearnerGraphAssumption,
               HasDepthDownward
          <6>q. SigS(Qd(al, y, 1)) \in Quorums(al)
            <7>1. HasDepth(al, y, 1) =
                    (/\ Sig(y) \in Acceptors
                     /\ IF 1 = 0 THEN (IsOneB(y) /\ Fresh(al, y))
                                 ELSE SigS(Qd(al, y, 1)) \in Quorums(al))
              BY <6>yM, <2>ar, <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDef
            <7> QED BY <7>1, <6>d1, <2>ar
          <6>sub. Qd(al, y, 1) \subseteq QU1
            <7> SUFFICES ASSUME NEW z \in Qd(al, y, 1)
                PROVE z \in QU1  OBVIOUS
            <7>1. z \in TranExclusive(y) /\ B(y) = B(z)
                    /\ HasDepth(al, z, 1 - 1)
              BY DEF Qd
            <7>2. z \in Tran(y)  BY <7>1 DEF TranExclusive
            <7>3. z \in U  BY <7>2, <6>y, <1>ucl
            <7>4. B(z) = CB(cand)  BY <7>1, <6>y
            <7>5. HasDepth(al, z, 0)  BY <7>1, <2>ar
            <7> QED BY <7>3, <7>4, <7>5
          <6>acc. SigS(QU1) \subseteq Acceptors
            <7> SUFFICES ASSUME NEW a \in SigS(QU1)
                PROVE a \in Acceptors  OBVIOUS
            <7>1. PICK z \in QU1 : a = Sig(z)  BY DEF SigS
            <7>2. z \in Messages /\ HasDepth(al, z, 0)  BY <1>uM
            <7>3. HasDepth(al, z, 0) =
                    (/\ Sig(z) \in Acceptors
                     /\ IF 0 = 0 THEN (IsOneB(z) /\ Fresh(al, z))
                                 ELSE SigS(Qd(al, z, 0)) \in Quorums(al))
              BY <7>2, <2>ar, <1>tok, <1>tt, <1>tf, <1>ta, HasDepthDef
            <7> QED BY <7>1, <7>2, <7>3
          <6>fin. IsFiniteSet(SigS(QU1))
            <7>1. QU1 \subseteq U  OBVIOUS
            <7>2. IsFiniteSet(QU1)  BY <7>1, <1>ufin, FS_Subset
            <7>3. SigS(QU1) = {Sig(z) : z \in QU1}  BY DEF SigS
            <7> QED BY <7>2, <7>3, FS_Image
          <6>ssub. SigS(Qd(al, y, 1)) \subseteq SigS(QU1)
            BY <6>sub DEF SigS
          <6>up. SigS(QU1) \in Quorums(al)
            BY <6>q, <6>ssub, <6>acc, <6>fin, QuorumUpward
          <6> QED BY <6>up, <5>1, <2>hd1
        <5> QED BY <5>1
      <4>bwd. CHasDepth(al, cand, 1) => sdr \in Acceptors  BY <2>hd1
      <4> QED BY <3>mem, <3>a, <4>fwd, <4>bwd
    <3>b. CASE ~(WFRRefFrontier(al, pl, r) >= 1)
      <4>d0. WFRRefFrontier(al, pl, r) = 0  BY <3>b, <3>D0nat, SMT
      <4>qd1. QU1 = WFRRefPending(al, pl, r)
        <5>sub. QU1 \subseteq WFRRefPending(al, pl, r)
          <6> SUFFICES ASSUME NEW z \in QU1
              PROVE z \in WFRRefPending(al, pl, r)  OBVIOUS
          <6>1. z \in U /\ B(z) = CB(cand) /\ HasDepth(al, z, 0)  OBVIOUS
          <6>2. HasDepth(al, z, WFRRefFrontier(al, pl, r))
            BY <6>1, <4>d0
          <6> QED BY <6>1, <6>2, <3>P0
        <5>sup. WFRRefPending(al, pl, r) \subseteq QU1
          <6> SUFFICES ASSUME NEW z \in WFRRefPending(al, pl, r)
              PROVE z \in QU1  OBVIOUS
          <6>1. z \in U /\ B(z) = CB(cand)
                  /\ HasDepth(al, z, WFRRefFrontier(al, pl, r))
            BY <3>P0
          <6>2. HasDepth(al, z, 0)  BY <6>1, <4>d0
          <6> QED BY <6>1, <6>2
        <5> QED BY <5>sub, <5>sup
      <4>csr. CSigS(WFRRefPending(al, pl, r)) = SigS(QU1)
        <5>1. QU1 \subseteq CMessages  BY <1>uMc
        <5>2. CSigS(QU1) = SigS(QU1)  BY <5>1, CSigSResolve
        <5> QED BY <5>2, <4>qd1
      <4>fwd. WFRBump(al, sdr, pl, r) => CHasDepth(al, cand, 1)
        <5>1. CASE WFRBump(al, sdr, pl, r)
          <6>1. sdr \in Acceptors
                  /\ CSigS(WFRRefPending(al, pl, r)) \in Quorums(al)
            BY <5>1 DEF WFRBump
          <6>2. SigS(QU1) \in Quorums(al)  BY <6>1, <4>csr
          <6> QED BY <6>1, <6>2, <2>hd1
        <5> QED BY <5>1
      <4>bwd. CHasDepth(al, cand, 1) => WFRBump(al, sdr, pl, r)
        <5>1. CASE CHasDepth(al, cand, 1)
          <6>1. sdr \in Acceptors /\ SigS(QU1) \in Quorums(al)
            BY <5>1, <2>hd1
          <6>2. CSigS(WFRRefPending(al, pl, r)) \in Quorums(al)
            BY <6>1, <4>csr
          <6> QED BY <6>1, <6>2 DEF WFRBump
        <5> QED BY <5>1
      <4> QED BY <3>mem, <3>b, <4>fwd, <4>bwd
    <3> QED BY <3>a, <3>b
  <2>B. CASE al \notin WFRQDom(pl, r)
    <3>1. al \notin WFRLrns(sdr, pl, r)  BY <2>B DEF WFRLrns
    <3>2. ~CHasDepth(al, cand, 1)
      <4>1. CASE CHasDepth(al, cand, 1)
        <5>1. SigS(QU1) \in Quorums(al)  BY <4>1, <2>hd1
        <5>2. SigS(QU1) # {}
          BY <5>1, LearnersMightAgree, ValidLearnerGraphAssumption,
             QuorumsHaveMembers
        <5>3. QU1 # {}  BY <5>2 DEF SigS
        <5>4. PICK z \in QU1 : TRUE  BY <5>3
        <5>5. z \in U /\ B(z) = CB(cand) /\ HasDepth(al, z, 0)  OBVIOUS
        <5>6. al \in WFRQDom(pl, r)  BY <5>5, <2>ar, <1>qdomchar
        <5> QED BY <5>6, <2>B
      <4> QED BY <4>1
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>A, <2>B
<1>lsub. WFRLrns(sdr, pl, r) \subseteq Learners
  BY DEF WFRLrns, WFRQDom
<1> QED BY <1>iff, <1>lsub
=============================================================================
