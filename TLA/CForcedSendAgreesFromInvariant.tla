------------------- MODULE CForcedSendAgreesFromInvariant -------------------
\* The forced-send agreement, from four facts about recent_messages that are
\* the content of the inductive invariant (and are hypotheses here).
\*
\* All three conjuncts: the built record is well formed exactly when the
\* abstract forced-send has a witness -- ANY witness certifies the built
\* record, since well-formedness of a non-proposal is determined by sender
\* and closure alone (CWellFormedSameTE); the built record is then itself a
\* witness (CBuiltInMessages / CBuiltTran supply that it is a real message
\* with history CAT(s,x)); and any CANONICAL witness IS the built record
\* (CWitnessUnique, whose canonicality hypothesis is the CSafeSentCanonical
\* invariant at the call sites).
EXTENDS HPaxosPlusCalConcrete, CBuiltTran, CBuiltInMessages, CReplyNotProposal,
        CWitnessUnique, CFields, CSigResolve, CTranResolve, CRefsResolve,
        CWellFormedSameTE, CTranExclRec, CMessageTranClosed, CFiniteTran,
        CMCShape, TLAPS

LEMMA CForcedSendAgreesFromInvariant ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption,
         NEW s \in SafeAcceptors, NEW x,
         Msgs \subseteq Messages,
         CRM(s, x) \subseteq Msgs,
         IsFiniteSet(CRM(s, x)),
         TranClosure(CRM(s, x)) = CAT(s, x),
         CRM(s, x) = CMMax(CAT(s, x))
  PROVE  CForcedSendAgreesAt(s, x)
<1> DEFINE rm == CRM(s, x)
<1> DEFINE T == CAT(s, x)
<1> DEFINE cand == [sender |-> s, payload |-> [type |-> "reply"], priors |-> rm]
<1> DEFINE W(y) == Sig(y) = s /\ TranExclusive(y) = T
<1>cmi. MessageInterface = CMI
  BY DEF ConcreteMessageInterface
<1>msg. Messages = CMessages /\ Proposals = CProposals /\ Senders = CSenders
  BY <1>cmi, CFields
<1>s. s \in CSenders
  BY DEF SafeAcceptorsAssumption, CSenders
<1>pl. [type |-> "reply"] \in CPayload
  BY DEF CPayload, CReply
<1>rm. rm \subseteq CMessages /\ IsFiniteSet(rm)
  BY <1>msg
<1>cand. cand = CCand(s, x)
  BY DEF CCand
\* The built record's history is exactly T.
<1>tex. CTranExcl(cand) = T
  <2>1. CTranExcl(cand) = UNION {CTran(p) : p \in rm}
    BY <1>s, <1>pl, <1>rm, CBuiltTran
  <2>2. \A p \in rm : Tran(p) = CTran(p)
    BY <1>cmi, <1>rm, CTranResolve
  <2>3. UNION {CTran(p) : p \in rm} = UNION {Tran(p) : p \in rm}
    BY <2>2
  <2> QED
    BY <2>1, <2>3 DEF TranClosure
<1>texU. UNION {CTran(p) : p \in rm} = T
  <2>1. CTranExcl(cand) = UNION {CTran(p) : p \in rm}
    BY <1>s, <1>pl, <1>rm, CBuiltTran
  <2> QED BY <2>1, <1>tex
<1>inmsg. cand \in CMessages <=> CWellFormed(cand)
  BY <1>s, <1>pl, <1>rm, CBuiltInMessages
\* Direction 1: CWellFormed(cand) supplies a witness, namely cand.
<1>fwd. CWellFormed(cand) => (cand \in (Messages \ Proposals) /\ W(cand))
  <2> SUFFICES ASSUME CWellFormed(cand)
               PROVE  cand \in (Messages \ Proposals) /\ W(cand)
    OBVIOUS
  <2>1. cand \in CMessages
    BY <1>inmsg
  <2>2. ~CIsProposal(cand)
    BY CReplyNotProposal DEF CIsProposal
  <2>3. cand \notin CProposals
    BY <2>1, <2>2 DEF CProposals
  <2>4. Sig(cand) = s
    BY <1>cmi, <2>1, CSigResolve DEF CSig
  <2>5. Tran(cand) = CTran(cand)
    BY <1>cmi, <2>1, CTranResolve
  <2>6. TranExclusive(cand) = CTranExcl(cand)
    BY <2>5 DEF TranExclusive, CTranExcl
  <2> QED
    BY <1>msg, <1>tex, <2>1, <2>3, <2>4, <2>6
\* Direction 2: every CANONICAL witness equals cand.
<1>uniq. \A y \in (Messages \ Proposals) :
           (W(y) /\ y.priors = Refs(y)) => y = cand
  <2> SUFFICES ASSUME NEW y \in (Messages \ Proposals), W(y),
                      y.priors = Refs(y)
               PROVE  y = cand
    OBVIOUS
  <2>1. y \in CMessages
    BY <1>msg
  <2>2. ~CIsProposal(y)
    BY <1>msg DEF CProposals
  <2>3. CSig(y) = s
    BY <1>cmi, <2>1, CSigResolve
  <2>4. Tran(y) = CTran(y)
    BY <1>cmi, <2>1, CTranResolve
  <2>5. CTranExcl(y) = T
    BY <2>4 DEF TranExclusive, CTranExcl
  <2>ref. y.priors = CRefs(y)
    BY <1>cmi, <2>1, CRefsResolve
  <2>6. y = [sender |-> CSig(y), payload |-> [type |-> "reply"],
             priors |-> CMMax(CTranExcl(y))]
    BY <2>1, <2>2, <2>ref, CWitnessUnique
  <2> QED
    BY <2>3, <2>5, <2>6
\* Any witness at all certifies the built record: well-formedness of a
\* non-proposal is determined by (sender, closure) alone.
<1>bic. CWellFormed(cand) <=> (\E y \in (Messages \ Proposals) : W(y))
  <2>1. CWellFormed(cand) => (\E y \in (Messages \ Proposals) : W(y))
    BY <1>fwd
  <2>2. (\E y \in (Messages \ Proposals) : W(y)) => CWellFormed(cand)
    <3> SUFFICES ASSUME NEW y \in (Messages \ Proposals), W(y)
                 PROVE  CWellFormed(cand)
      OBVIOUS
    <3>ycm. y \in CMessages
      BY <1>msg
    <3>ymc. y \in CMC
      BY <3>ycm, CMessagesSubMC
    <3>ynp. ~CIsProposal(y)
      BY <1>msg DEF CProposals
    <3>wfy. CWellFormed(y)
      <4>1. y \in CTran(y)  BY <3>ymc, CSelfInTran
      <4> QED BY <4>1, <3>ycm DEF CMessages
    <3>shape. y \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
      BY <3>ymc, CMCShape
    <3>ysnd. y.sender = s
      <4>1. CSig(y) = s  BY <1>cmi, <3>ycm, CSigResolve
      <4> QED BY <4>1 DEF CSig
    <3>ypl. y.payload = [type |-> "reply"]
      <4>1. y.payload \in CPayload  BY <3>shape
      <4>2. y.payload \notin CProposal  BY <3>ynp DEF CIsProposal
      <4>3. y.payload \in CReply  BY <4>1, <4>2 DEF CPayload
      <4> QED BY <4>3 DEF CReply
    <3>yrec. y = [sender |-> s, payload |-> [type |-> "reply"],
                  priors |-> y.priors]
      BY <3>shape, <3>ysnd, <3>ypl
    <3>yprsub. y.priors \subseteq CMessages
      <4>1. CPriors(y) \subseteq CTranExcl(y)  BY <3>ymc, CTranExclRec
      <4>2. CTran(y) \subseteq CMessages  BY <3>ycm, CMessageTranClosed
      <4> QED BY <4>1, <4>2 DEF CPriors, CTranExcl
    <3>yprfin. IsFiniteSet(y.priors)
      <4>1. CPriors(y) \subseteq CTranExcl(y)  BY <3>ymc, CTranExclRec
      <4>2. IsFiniteSet(CTran(y))  BY <3>ymc, CFiniteTran
      <4>3. IsFiniteSet(CTranExcl(y))  BY <4>2, FS_Subset DEF CTranExcl
      <4> QED BY <4>1, <4>3, FS_Subset DEF CPriors
    <3>yte. CTranExcl(y) = T
      <4>1. Tran(y) = CTran(y)  BY <1>cmi, <3>ycm, CTranResolve
      <4> QED BY <4>1 DEF TranExclusive, CTranExcl
    <3>uni. UNION {CTran(p) : p \in y.priors} = UNION {CTran(p) : p \in rm}
      <4>1. CTranExcl(y) = UNION {CTran(p) : p \in CPriors(y)}
        BY <3>ymc, CTranExclRec
      <4>2. UNION {CTran(p) : p \in y.priors} = T
        BY <4>1, <3>yte DEF CPriors
      <4> QED BY <4>2, <1>texU
    <3>wfyrec. CWellFormed([sender |-> s, payload |-> [type |-> "reply"],
                            priors |-> y.priors])
      BY <3>wfy, <3>yrec
    <3> QED
      BY <1>s, <1>pl, CReplyNotProposal, <3>yprsub, <3>yprfin, <1>rm,
         <3>uni, <3>wfyrec, CWellFormedSameTE
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>bic, <1>fwd, <1>uniq, <1>cand DEF CForcedSendAgreesAt
=============================================================================
