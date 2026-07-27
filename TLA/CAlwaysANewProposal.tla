-------------------------- MODULE CAlwaysANewProposal --------------------------
EXTENDS MessageConcrete, CFields, CBResolve, CUnionTranFiniteClosed,
        CMessagesSubMC, CGenTranRefs, CMCFromShape, CFreshTranExcl,
        CSelfInTran, CProposerSenderNotAcceptor, CTranReflexiveSplit,
        CBMonotone, CMessageTranClosed, CBTypeNat, CFiniteTran,
        CTranResolve, CSigResolve, MaxProps, FiniteSetTheorems

LEMMA CAlwaysANewProposal == ASSUME MessageInterface = CMI PROVE AlwaysANewProposal
<1> SUFFICES ASSUME NEW m \in SUBSET Messages, NEW b \in Ballots,
                    IsFiniteSet(m), \A x \in m : B(x) < b
             PROVE \E p \in Proposals :
                     /\ TranExclusive(p) = TranClosure(m)
                     /\ B(p) = b
                     /\ Sig(p) \notin Acceptors
  BY DEF AlwaysANewProposal
<1>msgeq. Messages = CMessages  BY CFields
<1>mmc. m \subseteq CMessages  BY <1>msgeq
<1>bhyp. \A x \in m : CB(x) < b
  <2> SUFFICES ASSUME NEW x \in m PROVE CB(x) < b  OBVIOUS
  <2>1. x \in CMessages  BY <1>mmc
  <2>2. B(x) = CB(x)  BY <2>1, CBResolve
  <2> QED BY <2>2

\* --- U, PP, prec construction ---
<1> DEFINE U == UNION {CTran(x) : x \in m}
<1>Uprops. IsFiniteSet(U) /\ U \subseteq CMessages /\ (\A z \in U : CTran(z) \subseteq U)
  BY <1>mmc, CUnionTranFiniteClosed
<1>Ufin. IsFiniteSet(U)  BY <1>Uprops
<1>Usub. U \subseteq CMessages  BY <1>Uprops
<1>Uclosed. \A z \in U : CTran(z) \subseteq U  BY <1>Uprops
<1>UsubCMC. U \subseteq CMC  BY <1>Usub, CMessagesSubMC

<1> DEFINE PP == CMMax(U)
<1>ppEq. U = UNION {CTran(x) : x \in PP}  BY <1>Ufin, <1>UsubCMC, <1>Uclosed, CGenTranRefs
<1>ppSub. PP \subseteq U  BY DEF CMMax
<1>ppSubCMC. PP \subseteq CMC  BY <1>ppSub, <1>UsubCMC
<1>ppFin. IsFiniteSet(PP)  BY <1>ppSub, <1>Ufin, FS_Subset

<1>bsend. CProposerSender \in CSenders  BY DEF CSenders
<1>bnat. b \in Nat  BY DEF Ballots
<1>bpay. [type |-> "proposal", ballot |-> b] \in CProposal  BY <1>bnat DEF CProposal
<1> DEFINE prec == [sender |-> CProposerSender, payload |-> [type |-> "proposal", ballot |-> b], priors |-> PP]
<1>precShape. prec \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
  BY <1>bsend, <1>bpay, <1>ppSubCMC DEF CPayload
<1>precMC. prec \in CMC  BY <1>precShape, <1>ppFin, CMCFromShape
<1>precPriors. prec.priors = PP  OBVIOUS
<1>precTE0. CTranExcl(prec) = UNION {CTran(q) : q \in PP}  BY <1>precMC, <1>precPriors, CFreshTranExcl
<1>precTEeqU. CTranExcl(prec) = U  BY <1>precTE0, <1>ppEq

\* --- CWellFormed(prec) ---
<1>precIsProp. CIsProposal(prec)  BY DEF CIsProposal, CProposal
<1>precSelf. prec \in CTran(prec)  BY <1>precMC, CSelfInTran
<1>precHasProp. \E a \in CTran(prec) : CIsProposal(a)  BY <1>precSelf, <1>precIsProp
<1>precSig. CSig(prec) = CProposerSender  BY DEF CSig
<1>precNotAcc. CProposerSender \notin Acceptors  BY CProposerSenderNotAcceptor
<1>precNotCaughtVac. CSig(prec) \in Acceptors => CSig(prec) \notin CCaught(prec)
  BY <1>precSig, <1>precNotAcc
<1>precDisj. CIsProposal(prec) \/ CIsOneB(prec) \/ CIsTwoA(prec)  BY <1>precIsProp

<1>precTranSplit. CTran(prec) = {prec} \cup U
  <2>1. CTran(prec) = {prec} \cup CTranExcl(prec)  BY <1>precMC, CTranReflexiveSplit
  <2> QED BY <2>1, <1>precTEeqU

<1>Uballots. \A y \in U : CB(y) < b
  <2> SUFFICES ASSUME NEW y \in U PROVE CB(y) < b  OBVIOUS
  <2>1. PICK x \in m : y \in CTran(x)  OBVIOUS
  <2>2. x \in CMessages  BY <1>mmc
  <2>3. CB(y) <= CB(x)  BY <2>2, <2>1, CBMonotone
  <2>4. CB(x) < b  BY <1>bhyp, <2>1
  <2>5. y \in CMessages  BY <2>2, <2>1, CMessageTranClosed
  <2>6. CB(y) \in Nat  BY <2>5, CBTypeNat
  <2>7. CB(x) \in Nat  BY <2>2, CBTypeNat
  <2> QED BY <2>3, <2>4, <1>bnat, <2>6, <2>7

<1>precFilterBallot. CIsProposal(prec) => CB(prec) = prec.payload.ballot
  <2> DEFINE PropSet == {w \in CTran(prec) : CIsProposal(w)}
  <2> DEFINE ImgSet == {w.payload.ballot : w \in PropSet}
  <2>eq. PropSet = {prec} \cup {w \in U : CIsProposal(w)}  BY <1>precTranSplit, <1>precIsProp
  <2>imgEq. ImgSet = {b} \cup {w.payload.ballot : w \in {w \in U : CIsProposal(w)}}  BY <2>eq
  <2>bInImg. b \in ImgSet
    <3>1. prec \in PropSet  BY <1>precSelf, <1>precIsProp, <2>eq
    <3>2. prec.payload.ballot = b  OBVIOUS
    <3> QED BY <3>1, <3>2
  <2>ub. \A z \in ImgSet : z <= b
    <3> SUFFICES ASSUME NEW z \in ImgSet PROVE z <= b  OBVIOUS
    <3>1. CASE z = b  BY <3>1, <1>bnat
    <3>2. CASE z # b
      <4>1. PICK w \in {w \in U : CIsProposal(w)} : z = w.payload.ballot  BY <2>imgEq, <3>2
      <4>2. w \in U  BY <4>1
      <4>3. w \in CMessages  BY <4>2, <1>Usub
      <4>4. CB(w) < b  BY <4>2, <1>Uballots
      <4>5. w \in CTran(w)  BY <4>3, CMessagesSubMC, CSelfInTran
      <4>6. \A zz \in CTran(w) : CWellFormed(zz)  BY <4>3 DEF CMessages
      <4>7. CWellFormed(w)  BY <4>5, <4>6
      <4>8. CFilterOut(w)  BY <4>7 DEF CWellFormed
      <4>9. CIsProposal(w) => CB(w) = w.payload.ballot  BY <4>8 DEF CFilterOut
      <4>10. w.payload.ballot = CB(w)  BY <4>1, <4>9
      <4> QED BY <4>1, <4>10, <4>4
    <3> QED BY <3>1, <3>2
  <2>finImg. IsFiniteSet(ImgSet)
    <3>1. IsFiniteSet(CTran(prec))  BY <1>precMC, CFiniteTran
    <3>2. IsFiniteSet(PropSet)  BY <3>1, FS_Subset
    <3> QED BY <3>2, FS_Image
  <2>neImg. ImgSet # {}  BY <2>bInImg
  <2>natImg. \A z \in ImgSet : z \in Nat
    <3> SUFFICES ASSUME NEW w \in PropSet PROVE w.payload.ballot \in Nat  OBVIOUS
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

<1>precFilterPriors. prec.priors = CRefs(prec)
  <2>1. CRefs(prec) = {x \in CTranExcl(prec) : (\A y \in CTranExcl(prec) : y = x \/ x \notin CTran(y))}
    BY DEF CRefs
  <2>2. CRefs(prec) = {x \in U : (\A y \in U : y = x \/ x \notin CTran(y))}  BY <2>1, <1>precTEeqU
  <2>3. CMMax(U) = {x \in U : \A y \in U : x \notin CTranExcl(y)}  BY DEF CMMax
  <2>4. \A x \in U : (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
    <3> SUFFICES ASSUME NEW x \in U
                 PROVE (\A y \in U : y = x \/ x \notin CTran(y)) <=> (\A y \in U : x \notin CTranExcl(y))
      OBVIOUS
    <3>1. ASSUME NEW y \in U PROVE (y = x \/ x \notin CTran(y)) <=> (x \notin CTranExcl(y))
      BY DEF CTranExcl
    <3> QED BY <3>1
  <2>5. CRefs(prec) = CMMax(U)  BY <2>2, <2>3, <2>4
  <2> QED BY <2>5, <1>precPriors

<1>precFilter. CFilterOut(prec)
  BY <1>precFilterBallot, <1>precFilterPriors DEF CFilterOut

<1>precWF. CWellFormed(prec)
  BY <1>precHasProp, <1>precNotCaughtVac, <1>precDisj, <1>precFilter DEF CWellFormed

<1>allWF. \A z \in CTran(prec) : CWellFormed(z)
  <2> SUFFICES ASSUME NEW z \in CTran(prec) PROVE CWellFormed(z)  OBVIOUS
  <2>1. CASE z = prec  BY <2>1, <1>precWF
  <2>2. CASE z \in U
    <3>1. z \in CMessages  BY <1>Usub, <2>2
    <3>2. z \in CTran(z)  BY <3>1, CMessagesSubMC, CSelfInTran
    <3>3. \A zz \in CTran(z) : CWellFormed(zz)  BY <3>1 DEF CMessages
    <3> QED BY <3>2, <3>3
  <2> QED BY <1>precTranSplit, <2>1, <2>2

<1>precInMessages. prec \in CMessages  BY <1>precMC, <1>allWF DEF CMessages
<1>precInProposals. prec \in CProposals  BY <1>precInMessages, <1>precIsProp DEF CProposals
<1>propEq. Proposals = CProposals  BY CFields

\* --- resolve back to abstract Tran/TranExclusive/B/TranClosure/Proposals ---
<1>precAbsTran. Tran(prec) = CTran(prec)  BY <1>precInMessages, CTranResolve
<1>precAbsTE. TranExclusive(prec) = CTranExcl(prec)
  BY <1>precAbsTran DEF TranExclusive, CTranExcl
<1>precAbsTE2. TranExclusive(prec) = U  BY <1>precAbsTE, <1>precTEeqU
<1>tcEq. TranClosure(m) = U
  <2>1. TranClosure(m) = UNION {Tran(x) : x \in m}  BY DEF TranClosure
  <2>2. \A x \in m : Tran(x) = CTran(x)
    <3> SUFFICES ASSUME NEW x \in m PROVE Tran(x) = CTran(x)  OBVIOUS
    <3>1. x \in CMessages  BY <1>mmc
    <3> QED BY <3>1, CTranResolve
  <2> QED BY <2>1, <2>2
<1>precAbsTE3. TranExclusive(prec) = TranClosure(m)  BY <1>precAbsTE2, <1>tcEq
<1>precAbsB. B(prec) = CB(prec)  BY <1>precInMessages, CBResolve
<1>precB. B(prec) = b  BY <1>precAbsB, <1>precFilterBallot, <1>precIsProp
<1>precAbsSig. Sig(prec) = CSig(prec)  BY <1>precInMessages, CSigResolve
<1>precSigNotAcc. Sig(prec) \notin Acceptors  BY <1>precAbsSig, <1>precSig, <1>precNotAcc
<1> QED BY <1>precInProposals, <1>propEq, <1>precAbsTE3, <1>precB, <1>precSigNotAcc
=============================================================================
