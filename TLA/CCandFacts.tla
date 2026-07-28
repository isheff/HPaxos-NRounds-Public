--------------------------- MODULE CCandFacts ---------------------------
\* What the built candidate looks like on a step, when it is well formed: it is
\* a real message, its strict history is exactly the enlarged knowledge set,
\* and it is signed by the acceptor taking the step.
EXTENDS HPaxosPlusCalConcrete, CUpGood, CRMIsMax, CTranClosureOfMax,
        CBuiltTran, CBuiltInMessages, CFields, CSigResolve, CTranResolve,
        FiniteSetTheorems, TLAPS

LEMMA CCandFacts ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption,
         NEW s \in SafeAcceptors, NEW x \in Messages,
         x \in Msgs, TranExclusive(x) \subseteq known_messages[s],
         CInv, KnownTranClosureInvT, SelfSentBoundedInvT, CRecentIsMax,
         CWellFormed(CCand(s, x))
  PROVE  LET Up == (known_messages[s] \cup {x}) \cup CSelfSent(s)
         IN  /\ CCand(s, x) \in Messages
             /\ TranExclusive(CCand(s, x)) = Up
             /\ Sig(CCand(s, x)) = s
             /\ CRM(s, x) \subseteq Msgs
             /\ CRM(s, x) = CMMax(Up)
<1> DEFINE Up   == (known_messages[s] \cup {x}) \cup CSelfSent(s)
<1> DEFINE rm   == CRM(s, x)
<1> DEFINE cand == CCand(s, x)
<1>cmi. MessageInterface = CMI
  BY DEF ConcreteMessageInterface
<1>msg. Messages = CMessages
  BY <1>cmi, CFields
<1>up. /\ Up \subseteq Messages
       /\ IsFiniteSet(Up)
       /\ \A z \in Up : Tran(z) \subseteq Up
       /\ Up \subseteq Msgs
  BY CUpGood
<1>rm. rm = CMMax(Up)
  BY CRMIsMax
<1>rmsub. rm \subseteq Up /\ rm \subseteq Msgs /\ rm \subseteq Messages
  BY <1>rm, <1>up DEF CMMax
<1>rmfin. IsFiniteSet(rm)
  BY <1>rmsub, <1>up, FS_Subset
<1>cl. TranClosure(rm) = Up
  BY <1>rm, <1>up, CTranClosureOfMax
<1>s. s \in CSenders
  BY DEF SafeAcceptorsAssumption, CSenders
<1>pl. [type |-> "reply"] \in CPayload
  BY DEF CPayload, CReply
<1>rmc. rm \subseteq CMessages
  BY <1>rmsub, <1>msg
<1>inmsg. cand \in CMessages
  <2>1. cand \in CMessages <=> CWellFormed(cand)
    BY <1>s, <1>pl, <1>rmc, <1>rmfin, CBuiltInMessages DEF CCand
  <2> QED
    BY <2>1
<1>tex. TranExclusive(cand) = Up
  <2>1. CTranExcl(cand) = UNION {CTran(p) : p \in rm}
    BY <1>s, <1>pl, <1>rmc, <1>rmfin, CBuiltTran DEF CCand
  <2>2. \A p \in rm : Tran(p) = CTran(p)
    BY <1>cmi, <1>rmc, CTranResolve
  <2>3. UNION {CTran(p) : p \in rm} = TranClosure(rm)
    BY <2>2 DEF TranClosure
  <2>4. Tran(cand) = CTran(cand)
    BY <1>cmi, <1>inmsg, CTranResolve
  <2>5. TranExclusive(cand) = CTranExcl(cand)
    BY <2>4 DEF TranExclusive, CTranExcl
  <2> QED
    BY <2>1, <2>3, <2>5, <1>cl
<1>sig. Sig(cand) = s
  BY <1>cmi, <1>inmsg, CSigResolve DEF CSig, CCand
<1> QED
  BY <1>msg, <1>inmsg, <1>tex, <1>sig, <1>rmsub, <1>rm
=============================================================================
