---------------------------- MODULE CAlwaysANewTwoA ----------------------------
EXTENDS MessageConcrete, CFields, CBResolve, CUnionTranFiniteClosed,
        CMessagesSubMC, CTranResolve, CHasDepthResolve, CSigSResolve,
        CDepthDownward, CQuorumNonEmpty, CBAchievedByProposal, CBMonotone,
        CMessageTranClosed, CBTypeNat, CGenTranRefs, CMCFromShape,
        CFreshTranExcl, CTranReflexiveSplit, CSelfInTran, CFiniteTran,
        CQdCompute, CIsTwoAResolve, CCaughtSResolve, CSigResolve,
        MaxProps, FiniteSetTheorems

LEMMA CAlwaysANewTwoA ==
  ASSUME MessageInterface = CMI, LearnersMightAgree, ValidLearnerGraphAssumption
  PROVE AlwaysANewTwoA
<1> SUFFICES ASSUME NEW m \in SUBSET Messages, NEW b \in Ballots, NEW a \in Acceptors,
                    NEW alpha \in Learners, NEW d \in (1..(MaxDepth(alpha))),
                    IsFiniteSet(m), \A x \in m : B(x) <= b,
                    a \notin CaughtS(TranClosure(m)),
                    SigS({x \in TranClosure(m) :
                            B(x) = b /\ HasDepth(alpha, x, d-1)}) \in Quorums(alpha)
             PROVE \E x \in Messages :
               (/\ x \in TranClosure(m) \/ TranClosure(m) = TranExclusive(x)
                /\ B(x) = b
                /\ Sig(x) = a
                /\ HasDepth(alpha, x, d)
                /\ a \notin Caught(x)
                /\ IsTwoA(x))
  BY DEF AlwaysANewTwoA
<1>dnat. d \in Nat /\ d >= 1  OBVIOUS
<1>d1nat. d - 1 \in Nat  BY <1>dnat
<1>msgeq. Messages = CMessages  BY CFields
<1>mmc. m \subseteq CMessages  BY <1>msgeq
<1>bnat. b \in Nat  BY DEF Ballots
<1>bhyp. \A x \in m : CB(x) <= b
  <2> SUFFICES ASSUME NEW x \in m PROVE CB(x) <= b  OBVIOUS
  <2>1. x \in CMessages  BY <1>mmc
  <2>2. B(x) = CB(x)  BY <2>1, CBResolve
  <2> QED BY <2>2

\* --- U construction ---
<1> DEFINE U == UNION {CTran(x) : x \in m}
<1>Uprops. IsFiniteSet(U) /\ U \subseteq CMessages /\ (\A z \in U : CTran(z) \subseteq U)
  BY <1>mmc, CUnionTranFiniteClosed
<1>Ufin. IsFiniteSet(U)  BY <1>Uprops
<1>Usub. U \subseteq CMessages  BY <1>Uprops
<1>Uclosed. \A z \in U : CTran(z) \subseteq U  BY <1>Uprops
<1>UsubCMC. U \subseteq CMC  BY <1>Usub, CMessagesSubMC
<1>tcEq. TranClosure(m) = U
  <2>1. TranClosure(m) = UNION {Tran(x) : x \in m}  BY DEF TranClosure
  <2>2. \A x \in m : Tran(x) = CTran(x)
    <3> SUFFICES ASSUME NEW x \in m PROVE Tran(x) = CTran(x)  OBVIOUS
    <3>1. x \in CMessages  BY <1>mmc
    <3> QED BY <3>1, CTranResolve
  <2> QED BY <2>1, <2>2

\* --- resolve the acceptor-filtered quorum hypothesis to concrete form ---
<1> DEFINE AF == {p \in U : CB(p) = b /\ CHasDepth(alpha, p, d-1)}
<1>AFeq. {x \in TranClosure(m) : B(x) = b /\ HasDepth(alpha, x, d-1)} = AF
  <2> SUFFICES ASSUME NEW x \in U
               PROVE (B(x) = b /\ HasDepth(alpha, x, d-1))
                 <=> (CB(x) = b /\ CHasDepth(alpha, x, d-1))
    BY <1>tcEq
  <2>xmsg. x \in CMessages  BY <1>Usub
  <2>bx. B(x) = CB(x)  BY <2>xmsg, CBResolve
  <2>hx. HasDepth(alpha, x, d-1) = CHasDepth(alpha, x, d-1)  BY <2>xmsg, <1>d1nat, CHasDepthResolve
  <2> QED BY <2>bx, <2>hx
<1>sigsResolve. SigS(AF) = CSigS(AF)
  <2>1. AF \subseteq CMessages  BY <1>Usub
  <2> QED BY <2>1, CSigSResolve
<1>AFquo. CSigS(AF) \in Quorums(alpha)
  <2>1. SigS({x \in TranClosure(m) : B(x) = b /\ HasDepth(alpha, x, d-1)}) \in Quorums(alpha)
    OBVIOUS
  <2>2. SigS(AF) \in Quorums(alpha)  BY <2>1, <1>AFeq
  <2> QED BY <2>2, <1>sigsResolve

\* --- downward closure: all depths 0..d-1 have a ballot-b quorum in U ---
<1>downward. \A i \in 0..(d-1) : CSigS({p \in U : CB(p) = b /\ CHasDepth(alpha, p, i)}) \in Quorums(alpha)
  BY <1>Ufin, <1>Usub, <1>Uclosed, <1>d1nat, <1>AFquo, CDepthDownward

\* --- a ballot-b proposal exists in U (via a depth-(d-1) witness) ---
<1>AFne. AF # {}
  <2>1. CSigS(AF) # {}  BY <1>AFquo, CQuorumNonEmpty
  <2> QED BY <2>1 DEF CSigS
<1>w1. PICK w1 \in AF : TRUE  BY <1>AFne
<1>w1U. w1 \in U /\ CB(w1) = b  BY <1>w1
<1>w1msg. w1 \in CMessages  BY <1>w1U, <1>Usub
<1>achieve. \E q \in CTran(w1) : CIsProposal(q) /\ q.payload.ballot = CB(w1)
  BY <1>w1msg, CBAchievedByProposal
<1> PICK q0 \in CTran(w1) : CIsProposal(q0) /\ q0.payload.ballot = CB(w1)  BY <1>achieve
<1>q0inU. q0 \in U  BY <1>w1U, <1>Uclosed
<1>q0prop. CIsProposal(q0) /\ q0.payload.ballot = b  BY <1>achieve, <1>w1U

<1>Uball. \A y \in U : CB(y) <= b
  <2> SUFFICES ASSUME NEW y \in U PROVE CB(y) <= b  OBVIOUS
  <2>1. PICK x \in m : y \in CTran(x)  OBVIOUS
  <2>2. x \in CMessages  BY <1>mmc
  <2>3. CB(y) <= CB(x)  BY <2>2, <2>1, CBMonotone
  <2>4. CB(x) <= b  BY <1>bhyp, <2>1
  <2>5. y \in CMessages  BY <2>2, <2>1, CMessageTranClosed
  <2>6. CB(y) \in Nat  BY <2>5, CBTypeNat
  <2>7. CB(x) \in Nat  BY <2>2, CBTypeNat
  <2> QED BY <2>3, <2>4, <1>bnat, <2>6, <2>7

\* --- build the fresh reply record xrec, signed by a ---
<1> DEFINE PP == CMMax(U)
<1>ppEq. U = UNION {CTran(x) : x \in PP}  BY <1>Ufin, <1>UsubCMC, <1>Uclosed, CGenTranRefs
<1>ppSub. PP \subseteq U  BY DEF CMMax
<1>ppSubCMC. PP \subseteq CMC  BY <1>ppSub, <1>UsubCMC
<1>ppFin. IsFiniteSet(PP)  BY <1>ppSub, <1>Ufin, FS_Subset
<1>asend. a \in CSenders  BY DEF CSenders
<1>replypay. [type |-> "reply"] \in CReply  BY DEF CReply
<1> DEFINE xrec == [sender |-> a, payload |-> [type |-> "reply"], priors |-> PP]
<1>xrecShape. xrec \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
  BY <1>asend, <1>replypay, <1>ppSubCMC DEF CPayload
<1>xrecMC. xrec \in CMC  BY <1>xrecShape, <1>ppFin, CMCFromShape
<1>xrecPriors. xrec.priors = PP  OBVIOUS
<1>xrecTE0. CTranExcl(xrec) = UNION {CTran(q) : q \in PP}  BY <1>xrecMC, <1>xrecPriors, CFreshTranExcl
<1>xrecTEeqU. CTranExcl(xrec) = U  BY <1>xrecTE0, <1>ppEq
<1>xrecTranSplit. CTran(xrec) = {xrec} \cup U
  <2>1. CTran(xrec) = {xrec} \cup CTranExcl(xrec)  BY <1>xrecMC, CTranReflexiveSplit
  <2> QED BY <2>1, <1>xrecTEeqU
<1>xrecNotInU. xrec \notin U  BY <1>xrecTEeqU DEF CTranExcl
<1>xrecIsReply. CIsReply(xrec)  BY <1>replypay DEF CIsReply
<1>xrecNotProp. ~CIsProposal(xrec)  BY <1>xrecIsReply DEF CIsProposal, CIsReply, CProposal, CReply
<1>xrecSig. CSig(xrec) = a  BY DEF CSig

\* --- CB(xrec) = b (max proposal ballot in U is b) ---
<1>xrecCB. CB(xrec) = b
  <2> DEFINE Px == {w \in CTran(xrec) : CIsProposal(w)}
  <2> DEFINE ImgSet == {w.payload.ballot : w \in Px}
  <2>PxEq. Px = {w \in U : CIsProposal(w)}  BY <1>xrecTranSplit, <1>xrecNotProp
  <2>bInImg. b \in ImgSet
    <3>1. q0 \in Px  BY <1>q0inU, <1>q0prop, <2>PxEq
    <3> QED BY <3>1, <1>q0prop
  <2>ub. \A z \in ImgSet : z <= b
    <3> SUFFICES ASSUME NEW z \in ImgSet PROVE z <= b  OBVIOUS
    <3>1. PICK w \in Px : z = w.payload.ballot  OBVIOUS
    <3>2. w \in U /\ CIsProposal(w)  BY <3>1, <2>PxEq
    <3>3. w \in CMessages  BY <3>2, <1>Usub
    <3>4. w \in CTran(w)  BY <3>3, CMessagesSubMC, CSelfInTran
    <3>5. \A zz \in CTran(w) : CWellFormed(zz)  BY <3>3 DEF CMessages
    <3>6. CWellFormed(w)  BY <3>4, <3>5
    <3>7. CFilterOut(w)  BY <3>6 DEF CWellFormed
    <3>8. CIsProposal(w) => CB(w) = w.payload.ballot  BY <3>7 DEF CFilterOut
    <3>9. w.payload.ballot = CB(w)  BY <3>2, <3>8
    <3>10. CB(w) <= b  BY <3>2, <1>Uball
    <3> QED BY <3>1, <3>9, <3>10
  <2>finImg. IsFiniteSet(ImgSet)
    <3>1. IsFiniteSet(CTran(xrec))  BY <1>xrecMC, CFiniteTran
    <3>2. IsFiniteSet(Px)  BY <3>1, FS_Subset
    <3> QED BY <3>2, FS_Image
  <2>neImg. ImgSet # {}  BY <2>bInImg
  <2>natImg. \A z \in ImgSet : z \in Nat
    <3> SUFFICES ASSUME NEW w \in Px PROVE w.payload.ballot \in Nat  OBVIOUS
    <3>b. w.payload \in CProposal  BY DEF CIsProposal
    <3>c. PICK bb \in Ballots : w.payload = [type |-> "proposal", ballot |-> bb]  BY <3>b DEF CProposal
    <3>d. w.payload.ballot = bb  BY <3>c
    <3>e. bb \in Nat  BY DEF Ballots
    <3> QED BY <3>d, <3>e
  <2>maxprops. Max(ImgSet) \in ImgSet /\ (\A y \in ImgSet : Max(ImgSet) >= y)
    BY <2>finImg, <2>neImg, <2>natImg, MaxProps
  <2>maxNat. Max(ImgSet) \in Nat  BY <2>maxprops, <2>natImg
  <2>maxIsB. Max(ImgSet) = b
    <3>1. Max(ImgSet) <= b  BY <2>maxprops, <2>ub
    <3>2. Max(ImgSet) >= b  BY <2>maxprops, <2>bInImg
    <3> QED BY <3>1, <3>2, <2>maxNat, <1>bnat
  <2> QED BY <2>maxIsB DEF CB

\* --- CHasDepth(alpha, xrec, k) for every k in 1..d ---
<1>xrecDepth. \A k \in 1..d : CHasDepth(alpha, xrec, k)
  <2> SUFFICES ASSUME NEW k \in 1..d PROVE CHasDepth(alpha, xrec, k)  OBVIOUS
  <2>knat. k \in Nat /\ k >= 1 /\ k <= d  BY <1>dnat
  <2>qd. CCfl(xrec).qd[<<alpha, k>>] = {p \in CTranExcl(xrec) : CB(p) = CB(xrec) /\ CHasDepth(alpha, p, k-1)}
    BY <1>xrecMC, <2>knat, CQdCompute
  <2>qdU. CCfl(xrec).qd[<<alpha, k>>] = {p \in U : CB(p) = b /\ CHasDepth(alpha, p, k-1)}
    BY <2>qd, <1>xrecTEeqU, <1>xrecCB
  <2>k1. k-1 \in 0..(d-1)  BY <2>knat
  <2>quo. CSigS({p \in U : CB(p) = b /\ CHasDepth(alpha, p, k-1)}) \in Quorums(alpha)
    BY <2>k1, <1>downward
  <2>hd. CHasDepth(alpha, xrec, k) = (CSig(xrec) \in Acceptors /\ CSigS(CCfl(xrec).qd[<<alpha,k>>]) \in Quorums(alpha))
    <3>1. k # 0  BY <2>knat
    <3> QED BY <3>1 DEF CHasDepth
  <2> QED BY <2>hd, <1>xrecSig, <2>qdU, <2>quo
<1>xrecHasD. CHasDepth(alpha, xrec, d)  BY <1>xrecDepth, <1>dnat
<1>xrecHas1. CHasDepth(alpha, xrec, 1)  BY <1>xrecDepth, <1>dnat

\* --- xrec is a TwoA ---
<1>xrecTwoA. CIsTwoA(xrec)  BY <1>xrecNotProp, <1>xrecHas1 DEF CIsTwoA

\* --- xrec.priors = CRefs(xrec) ---
<1>xrecFilterPriors. xrec.priors = CRefs(xrec)
  <2>1. CRefs(xrec) = {x \in CTranExcl(xrec) : (\A y \in CTranExcl(xrec) : y = x \/ x \notin CTran(y))}
    BY DEF CRefs
  <2>2. CRefs(xrec) = {x \in U : (\A y \in U : y = x \/ x \notin CTran(y))}  BY <2>1, <1>xrecTEeqU
  <2>3. CMMax(U) = {x \in U : \A y \in U : x \notin CTranExcl(y)}  BY DEF CMMax
  <2>4. \A x \in U : (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
    <3> SUFFICES ASSUME NEW x \in U
                 PROVE (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
      OBVIOUS
    <3>1. ASSUME NEW y \in U PROVE (y = x \/ x \notin CTran(y)) <=> (x \notin CTranExcl(y))
      BY DEF CTranExcl
    <3> QED BY <3>1
  <2>5. CRefs(xrec) = CMMax(U)  BY <2>2, <2>3, <2>4
  <2> QED BY <2>5, <1>xrecPriors
<1>xrecFilterProp. CIsProposal(xrec) => CB(xrec) = xrec.payload.ballot  BY <1>xrecNotProp
<1>xrecFilter. CFilterOut(xrec)  BY <1>xrecFilterProp, <1>xrecFilterPriors DEF CFilterOut

\* --- has-a-proposal ---
<1>xrecHasProp. \E qq \in CTran(xrec) : CIsProposal(qq)
  <2>1. q0 \in CTran(xrec)  BY <1>q0inU, <1>xrecTranSplit
  <2> QED BY <2>1, <1>q0prop

\* --- not caught ---
<1>caughtSResolve. CaughtS(U) = CCaughtS(U)  BY <1>Usub, CCaughtSResolve
<1>abscaughtU. a \notin CaughtS(U)
  <2>1. a \notin CaughtS(TranClosure(m))  OBVIOUS
  <2> QED BY <2>1, <1>tcEq
<1>conccaughtU. a \notin CCaughtS(U)  BY <1>abscaughtU, <1>caughtSResolve
<1>notcaught. a \notin CCaughtS(CTran(xrec))
  <2> SUFFICES ASSUME NEW m1 \in CTran(xrec), NEW m2 \in CTran(xrec), CSig(m1) = a, CSig(m2) = a
               PROVE m1 \in CTran(m2) \/ m2 \in CTran(m1)
    BY DEF CCaughtS
  <2>1. CASE m1 \in U /\ m2 \in U
    <3> SUFFICES ASSUME ~(m1 \in CTran(m2) \/ m2 \in CTran(m1)) PROVE FALSE  OBVIOUS
    <3>1. m1 \notin CTran(m2) /\ m2 \notin CTran(m1)  OBVIOUS
    <3>2. a \in CCaughtS(U)  BY <2>1, <3>1 DEF CCaughtS
    <3> QED BY <3>2, <1>conccaughtU
  <2>2. CASE m1 = xrec
    <3>0. m2 \in U \/ m2 = xrec  BY <1>xrecTranSplit
    <3>1. CASE m2 \in U
      <4>1. m2 \in CTran(xrec)  BY <3>1, <1>xrecTranSplit
      <4> QED BY <2>2, <4>1
    <3>2. CASE m2 = xrec
      <4>1. xrec \in CTran(xrec)  BY <1>xrecMC, CSelfInTran
      <4> QED BY <2>2, <3>2, <4>1
    <3> QED BY <3>0, <3>1, <3>2
  <2>3. CASE m2 = xrec
    <3>0. m1 \in U \/ m1 = xrec  BY <1>xrecTranSplit
    <3>1. CASE m1 \in U
      <4>1. m1 \in CTran(xrec)  BY <3>1, <1>xrecTranSplit
      <4> QED BY <2>3, <4>1
    <3>2. CASE m1 = xrec
      <4>1. xrec \in CTran(xrec)  BY <1>xrecMC, CSelfInTran
      <4> QED BY <2>3, <3>2, <4>1
    <3> QED BY <3>0, <3>1, <3>2
  <2>0. (m1 \in U \/ m1 = xrec) /\ (m2 \in U \/ m2 = xrec)  BY <1>xrecTranSplit
  <2> QED BY <2>0, <2>1, <2>2, <2>3, <1>xrecTranSplit

\* --- CWellFormed(xrec) ---
<1>xrecNotCaughtVac. CSig(xrec) \in Acceptors => CSig(xrec) \notin CCaught(xrec)
  BY <1>xrecSig, <1>notcaught DEF CCaught
<1>xrecDisj. CIsProposal(xrec) \/ CIsOneB(xrec) \/ CIsTwoA(xrec)  BY <1>xrecTwoA
<1>xrecWF. CWellFormed(xrec)
  BY <1>xrecHasProp, <1>xrecNotCaughtVac, <1>xrecDisj, <1>xrecFilter DEF CWellFormed
<1>allWF. \A z \in CTran(xrec) : CWellFormed(z)
  <2> SUFFICES ASSUME NEW z \in CTran(xrec) PROVE CWellFormed(z)  OBVIOUS
  <2>1. CASE z = xrec  BY <2>1, <1>xrecWF
  <2>2. CASE z \in U
    <3>1. z \in CMessages  BY <1>Usub, <2>2
    <3>2. z \in CTran(z)  BY <3>1, CMessagesSubMC, CSelfInTran
    <3>3. \A zz \in CTran(z) : CWellFormed(zz)  BY <3>1 DEF CMessages
    <3> QED BY <3>2, <3>3
  <2> QED BY <1>xrecTranSplit, <2>1, <2>2
<1>xrecInMessages. xrec \in CMessages  BY <1>xrecMC, <1>allWF DEF CMessages

\* --- resolve back to abstract ---
<1>xrecAbsSig. Sig(xrec) = a  BY <1>xrecInMessages, CSigResolve, <1>xrecSig
<1>xrecAbsTran. Tran(xrec) = CTran(xrec)  BY <1>xrecInMessages, CTranResolve
<1>xrecAbsTE. TranExclusive(xrec) = CTranExcl(xrec)
  BY <1>xrecAbsTran DEF TranExclusive, CTranExcl
<1>xrecAbsTE2. TranExclusive(xrec) = TranClosure(m)  BY <1>xrecAbsTE, <1>xrecTEeqU, <1>tcEq
<1>xrecAbsB. B(xrec) = CB(xrec)  BY <1>xrecInMessages, CBResolve
<1>xrecAbsBb. B(xrec) = b  BY <1>xrecAbsB, <1>xrecCB
<1>xrecAbsHasD. HasDepth(alpha, xrec, d) = CHasDepth(alpha, xrec, d)
  BY <1>xrecInMessages, <1>dnat, CHasDepthResolve
<1>xrecAbsHasDd. HasDepth(alpha, xrec, d)  BY <1>xrecAbsHasD, <1>xrecHasD
<1>xrecAbsIsTwoA. IsTwoA(xrec) = CIsTwoA(xrec)  BY <1>xrecInMessages, CIsTwoAResolve
<1>xrecAbsTwoA. IsTwoA(xrec)  BY <1>xrecAbsIsTwoA, <1>xrecTwoA
<1>xrecAbsCaughtS. CaughtS(CTran(xrec)) = CCaughtS(CTran(xrec))
  <2>1. CTran(xrec) \subseteq CMessages  BY <1>xrecInMessages, CMessageTranClosed
  <2> QED BY <2>1, CCaughtSResolve
<1>xrecAbsCaught. Caught(xrec) = CCaughtS(CTran(xrec))
  BY <1>xrecAbsTran, <1>xrecAbsCaughtS DEF Caught
<1>xrecAbsNotCaught. a \notin Caught(xrec)  BY <1>xrecAbsCaught, <1>notcaught
<1> QED
  BY <1>msgeq, <1>xrecInMessages, <1>xrecAbsSig, <1>xrecAbsBb, <1>xrecAbsHasDd,
     <1>xrecAbsNotCaught, <1>xrecAbsTwoA, <1>xrecAbsTE2
=============================================================================
