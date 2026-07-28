------------------- MODULE CForcedSendAgreesFromInvariant -------------------
\* The forced-send agreement, from four facts about recent_messages that are
\* the content of the inductive invariant (and are hypotheses here).
\*
\* Both directions: the built record is well formed exactly when the abstract
\* forced-send has a witness (CBuiltInMessages / CBuiltTran supply that the
\* record is a real message with history CAT(s,x)), and any witness IS that
\* record (CWitnessUnique).  The CHOOSE identification falls out of uniqueness.
EXTENDS HPaxosPlusCalConcrete, CBuiltTran, CBuiltInMessages, CReplyNotProposal,
        CWitnessUnique, CFields, CSigResolve, CTranResolve, TLAPS

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
\* Direction 2: every witness equals cand.
<1>uniq. \A y \in (Messages \ Proposals) : W(y) => y = cand
  <2> SUFFICES ASSUME NEW y \in (Messages \ Proposals), W(y)
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
  <2>6. y = [sender |-> CSig(y), payload |-> [type |-> "reply"],
             priors |-> CMMax(CTranExcl(y))]
    BY <2>1, <2>2, CWitnessUnique
  <2> QED
    BY <2>3, <2>5, <2>6
<1>bic. CWellFormed(cand) <=> (\E y \in (Messages \ Proposals) : W(y))
  <2>1. CWellFormed(cand) => (\E y \in (Messages \ Proposals) : W(y))
    BY <1>fwd
  <2>2. (\E y \in (Messages \ Proposals) : W(y)) => CWellFormed(cand)
    <3> SUFFICES ASSUME NEW y \in (Messages \ Proposals), W(y)
                 PROVE  CWellFormed(cand)
      OBVIOUS
    <3>1. y = cand
      BY <1>uniq
    <3>2. cand \in CMessages
      BY <1>msg, <3>1
    <3> QED
      BY <1>inmsg, <3>2
  <2> QED
    BY <2>1, <2>2
<1>ch. CWellFormed(cand) => cand = (CHOOSE y \in (Messages \ Proposals) : W(y))
  <2> SUFFICES ASSUME CWellFormed(cand)
               PROVE  cand = (CHOOSE y \in (Messages \ Proposals) : W(y))
    OBVIOUS
  <2>1. \E y \in (Messages \ Proposals) : W(y)
    BY <1>bic
  <2>2. /\ (CHOOSE y \in (Messages \ Proposals) : W(y)) \in (Messages \ Proposals)
        /\ W(CHOOSE y \in (Messages \ Proposals) : W(y))
    BY <2>1
  <2> QED
    BY <1>uniq, <2>2
<1> QED
  BY <1>bic, <1>ch, <1>cand DEF CForcedSendAgreesAt
=============================================================================
