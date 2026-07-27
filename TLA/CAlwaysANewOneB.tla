---------------------------- MODULE CAlwaysANewOneB ----------------------------
EXTENDS MessageConcrete, CFields, CBResolve, CUnionTranFiniteClosed,
        CMessagesSubMC, CTranResolve, CCardOneWitness, CBMonotone,
        CMessageTranClosed, CBTypeNat, CBAchievedByProposal, CSelfInTran,
        CGenTranRefs, CMCFromShape, CFreshTranExcl, CTranReflexiveSplit,
        CFiniteTran, CCaughtSResolve, CSigResolve, MaxProps, FiniteSetTheorems

LEMMA CAlwaysANewOneB ==
  ASSUME MessageInterface = CMI, LearnersMightAgree, ValidLearnerGraphAssumption
  PROVE AlwaysANewOneB
<1> SUFFICES ASSUME NEW m \in SUBSET Messages, NEW b \in Ballots, NEW a \in Acceptors,
                    IsFiniteSet(m), \A x \in m : B(x) <= b,
                    Cardinality({x \in TranClosure(m) : B(x) = b}) = 1,
                    a \notin CaughtS(TranClosure(m))
             PROVE \E x \in Messages :
               (/\ Sig(x) = a
                /\ a \notin Caught(x)
                /\ IsOneB(x)
                /\ TranExclusive(x) = TranClosure(m))
  BY DEF AlwaysANewOneB
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

\* --- resolve the Cardinality=1 hypothesis to concrete terms, extract w0 ---
<1>cardsetEq. {x \in TranClosure(m) : B(x) = b} = {x \in U : CB(x) = b}
  <2>1. \A x \in U : B(x) = CB(x)  BY <1>Usub, CBResolve
  <2> QED BY <1>tcEq, <2>1
<1>cardhyp. Cardinality({x \in U : CB(x) = b}) = 1  BY <1>cardsetEq
<1>Ufinset. IsFiniteSet({x \in U : CB(x) = b})  BY <1>Ufin, FS_Subset
<1> PICK w0 : {x \in U : CB(x) = b} = {w0}  BY CCardOneWitness, <1>Ufinset, <1>cardhyp
<1>w0set. {x \in U : CB(x) = b} = {w0}  OBVIOUS
<1>w0mem. w0 \in {x \in U : CB(x) = b}  BY <1>w0set
<1>w0inU. w0 \in U /\ CB(w0) = b  BY <1>w0mem
<1>w0uniq. \A y \in U : CB(y) = b => y = w0
  <2> SUFFICES ASSUME NEW y \in U, CB(y) = b PROVE y = w0  OBVIOUS
  <2>1. y \in {x \in U : CB(x) = b}  OBVIOUS
  <2> QED BY <2>1, <1>w0set

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

\* --- w0 must be a proposal ---
<1>w0msg. w0 \in CMessages  BY <1>Usub, <1>w0inU
<1>achieve. \E q \in CTran(w0) : CIsProposal(q) /\ q.payload.ballot = CB(w0)
  BY <1>w0msg, CBAchievedByProposal
<1> PICK q0 \in CTran(w0) : CIsProposal(q0) /\ q0.payload.ballot = CB(w0)  BY <1>achieve
<1>w0mc. w0 \in CMC  BY <1>w0msg, CMessagesSubMC
<1>q0inU. q0 \in U  BY <1>w0inU, <1>Uclosed
<1>q0msg. q0 \in CMessages  BY <1>q0inU, <1>Usub
<1>q0wf. CWellFormed(q0)
  <2>0. q0 \in CTran(q0)  BY <1>q0msg, CMessagesSubMC, CSelfInTran
  <2>wf. \A zz \in CTran(q0) : CWellFormed(zz)  BY <1>q0msg DEF CMessages
  <2> QED BY <2>0, <2>wf
<1>q0filter. CFilterOut(q0)  BY <1>q0wf DEF CWellFormed
<1>q0cb. CB(q0) = q0.payload.ballot  BY <1>achieve, <1>q0filter DEF CFilterOut
<1>q0cbb. CB(q0) = b  BY <1>q0cb, <1>achieve, <1>w0inU
<1>q0eqw0. q0 = w0  BY <1>q0inU, <1>q0cbb, <1>w0uniq
<1>w0isprop. CIsProposal(w0)  BY <1>q0eqw0, <1>achieve
<1>w0notreply. ~CIsReply(w0)  BY <1>w0isprop DEF CIsProposal, CIsReply, CProposal, CReply
\* w0 is a proposal, and OneBs are non-proposals, so w0 is not a OneB.
<1>w0notoneb. ~CIsOneB(w0)  BY <1>w0isprop DEF CIsOneB
<1>w0payb. w0.payload.ballot = b  BY <1>q0eqw0, <1>achieve, <1>w0inU

\* --- build the fresh reply record xrec ---
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
<1>xrecTE0. CTranExcl(xrec) = UNION {CTran(q) : q \in PP}
  BY <1>xrecMC, <1>xrecPriors, CFreshTranExcl
<1>xrecTEeqU. CTranExcl(xrec) = U  BY <1>xrecTE0, <1>ppEq
<1>xrecTranSplit. CTran(xrec) = {xrec} \cup U
  <2>1. CTran(xrec) = {xrec} \cup CTranExcl(xrec)  BY <1>xrecMC, CTranReflexiveSplit
  <2> QED BY <2>1, <1>xrecTEeqU
<1>xrecNotInU. xrec \notin U  BY <1>xrecTEeqU DEF CTranExcl

<1>xrecIsReply. CIsReply(xrec)  BY <1>replypay DEF CIsReply
<1>xrecNotProp. ~CIsProposal(xrec)
  BY <1>xrecIsReply DEF CIsProposal, CIsReply, CProposal, CReply

\* --- CB(xrec) = b ---
<1>xrecCB. CB(xrec) = b
  <2> DEFINE Px == {w \in CTran(xrec) : CIsProposal(w)}
  <2> DEFINE ImgSet == {w.payload.ballot : w \in Px}
  <2>PxEq. Px = {w \in U : CIsProposal(w)}  BY <1>xrecTranSplit, <1>xrecNotProp
  <2>bInImg. b \in ImgSet
    <3>1. w0 \in Px  BY <1>w0inU, <1>w0isprop, <2>PxEq
    <3> QED BY <3>1, <1>w0payb
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

\* --- xrec is OneB ---
<1>matchset. {y \in CTran(xrec) : CB(y) = b} = {xrec, w0}
  <2>1. {y \in U : CB(y) = b} = {w0}  BY <1>w0set
  <2> QED BY <1>xrecTranSplit, <1>xrecCB, <2>1
<1>xrecNEw0. xrec # w0  BY <1>xrecNotInU, <1>w0inU
<1>card2. Cardinality({xrec, w0}) = 2
  <2>1. Cardinality({xrec}) = 1  BY FS_Singleton
  <2>2. IsFiniteSet({xrec})  BY FS_Singleton
  <2>3. w0 \notin {xrec}  BY <1>xrecNEw0
  <2>4. {xrec, w0} = {xrec} \cup {w0}  OBVIOUS
  <2>5. Cardinality({xrec} \cup {w0}) = Cardinality({xrec}) + 1  BY <2>2, <2>3, FS_AddElement
  <2> QED BY <2>1, <2>4, <2>5
<1>xrecOneB. CIsOneB(xrec)  BY <1>xrecNotProp, <1>matchset, <1>card2, <1>xrecCB DEF CIsOneB

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

\* --- CFilterOut(xrec) ---
<1>xrecFilterProp. CIsProposal(xrec) => CB(xrec) = xrec.payload.ballot  BY <1>xrecNotProp
<1>xrecFilter. CFilterOut(xrec)
  BY <1>xrecFilterProp, <1>xrecFilterPriors DEF CFilterOut

\* --- has-a-proposal witness ---
<1>xrecHasProp. \E qq \in CTran(xrec) : CIsProposal(qq)
  <2>1. w0 \in CTran(xrec)  BY <1>w0inU, <1>xrecTranSplit
  <2> QED BY <2>1, <1>w0isprop

\* --- sig / not-caught ---
<1>xrecSig. CSig(xrec) = a  BY DEF CSig
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
<1>xrecDisj. CIsProposal(xrec) \/ CIsOneB(xrec) \/ CIsTwoA(xrec)  BY <1>xrecOneB
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
<1>xrecAbsCaughtS. CaughtS(CTran(xrec)) = CCaughtS(CTran(xrec))
  <2>1. CTran(xrec) \subseteq CMessages  BY <1>xrecInMessages, CMessageTranClosed
  <2> QED BY <2>1, CCaughtSResolve
<1>xrecAbsCaught. Caught(xrec) = CCaughtS(CTran(xrec))
  BY <1>xrecAbsTran, <1>xrecAbsCaughtS DEF Caught
<1>xrecAbsNotCaught. a \notin Caught(xrec)  BY <1>xrecAbsCaught, <1>notcaught
<1>xrecAbsIsOneB. IsOneB(xrec)
  <2>1. IsOneB(xrec) = (~IsProposal(xrec) /\ Cardinality({x \in Tran(xrec) : B(x) = B(xrec)}) = 2)
    BY DEF IsOneB
  <2>np. ~IsProposal(xrec)
    <3>1. Proposals = CProposals  BY CFields
    <3>2. xrec \notin CProposals  BY <1>xrecNotProp, <1>xrecInMessages DEF CProposals
    <3> QED BY <3>1, <3>2 DEF IsProposal
  <2>2. \A x \in Tran(xrec) : x \in CMessages
    <3>1. Tran(xrec) = CTran(xrec)  BY <1>xrecAbsTran
    <3> QED BY <3>1, <1>xrecInMessages, CMessageTranClosed
  <2>3. \A x \in Tran(xrec) : B(x) = CB(x)  BY <2>2, CBResolve
  <2>4. B(xrec) = CB(xrec)  BY <1>xrecInMessages, CBResolve
  <2>5. {x \in Tran(xrec) : B(x) = B(xrec)} = {x \in CTran(xrec) : CB(x) = CB(xrec)}
    BY <1>xrecAbsTran, <2>3, <2>4
  <2> QED BY <2>1, <2>np, <2>5, <1>matchset, <1>card2, <1>xrecCB
<1> QED BY <1>msgeq, <1>xrecInMessages, <1>xrecAbsSig, <1>xrecAbsNotCaught, <1>xrecAbsIsOneB, <1>xrecAbsTE2
=============================================================================
