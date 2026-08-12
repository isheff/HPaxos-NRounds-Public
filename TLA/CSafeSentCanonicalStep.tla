------------------------ MODULE CSafeSentCanonicalStep ------------------------
\* Canonicality of safe sends is preserved by every concrete step.  A safe
\* acceptor only ever adds the record it BUILDS, whose priors are the maximal
\* antichain of its own history (CCandFacts + CRefsIsMMax); a byz sender's
\* message is not signed by a safe acceptor, so the invariant does not speak
\* to it.
EXTENDS HPaxosPlusCalConcrete, CSafeGuardsIdentical, CCandFacts, CRefsResolve,
        CRefsIsMMax, CTranResolve, CFields, TLAPS

LEMMA CSafeSentCanonicalStep ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption,
         CJoint, CSafeSentCanonical, [CNext]_CVars
  PROVE  CSafeSentCanonical'
<1>inv. CInv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ CRecentIsMax
  BY DEF CJoint
<1>cmi. MessageInterface = CMI
  BY DEF ConcreteMessageInterface
<1>1. CASE \E self \in SafeAcceptors \times Messages : CSafeStep(self)
  <2> PICK self \in SafeAcceptors \times Messages : CSafeStep(self)
    BY <1>1
  <2>1. self[1] \in SafeAcceptors /\ self[2] \in Messages
          /\ self = <<self[1], self[2]>>
    OBVIOUS
  <2> DEFINE s == self[1]
  <2> DEFINE x == self[2]
  <2> DEFINE cand == CCand(s, x)
  <2>g. x \in Msgs /\ TranExclusive(x) \subseteq known_messages[s]
    BY <2>1, CSafeGuardsIdentical
  <2>A. CASE CWellFormed(CCand(s, x))
    <3>facts. /\ cand \in Messages
              /\ TranExclusive(cand)
                   = (known_messages[s] \cup {x}) \cup CSelfSent(s)
              /\ Sig(cand) = s
              /\ CRM(s, x) \subseteq Msgs
              /\ CRM(s, x) = CMMax((known_messages[s] \cup {x}) \cup CSelfSent(s))
      BY <2>1, <2>g, <1>inv, <2>A, CCandFacts
    <3>net. Msgs' = Msgs \cup {cand}
      BY <2>1, <2>A DEF CSafeStep, CCand, CRM
    <3>can. cand.priors = Refs(cand)
      <4>1. cand.priors = CRM(s, x)
        BY DEF CCand
      <4>3. cand \in CMessages
        BY <3>facts, <1>cmi, CFields
      <4>4. Tran(cand) = CTran(cand)
        BY <4>3, <1>cmi, CTranResolve
      <4>5. CTranExcl(cand) = TranExclusive(cand)
        BY <4>4 DEF TranExclusive, CTranExcl
      <4>6. Refs(cand) = CRefs(cand)
        BY <4>3, <1>cmi, CRefsResolve
      <4>7. CRefs(cand) = CMMax(CTranExcl(cand))
        BY CRefsIsMMax
      <4>8. CMMax(CTranExcl(cand))
              = CMMax((known_messages[s] \cup {x}) \cup CSelfSent(s))
        BY <4>5, <3>facts
      <4> QED
        BY <4>1, <4>6, <4>7, <4>8, <3>facts
    <3>new. \A m \in Msgs' : Sig(m) \in SafeAcceptors => m.priors = Refs(m)
      <4> SUFFICES ASSUME NEW m \in Msgs', Sig(m) \in SafeAcceptors
          PROVE m.priors = Refs(m)
        OBVIOUS
      <4>a. CASE m \in Msgs
        BY <4>a DEF CSafeSentCanonical
      <4>b. CASE m = cand
        BY <4>b, <3>can
      <4> QED BY <3>net, <4>a, <4>b
    <3> QED BY <3>new DEF CSafeSentCanonical
  <2>B. CASE ~CWellFormed(CCand(s, x))
    <3>net. Msgs' = Msgs
      BY <2>1, <2>B DEF CSafeStep, CCand, CRM
    <3> QED BY <3>net, CSafeSentCanonical DEF CSafeSentCanonical
  <2> QED BY <2>A, <2>B
<1>2. CASE \E self \in ByzSenders : CByzStep(self)
  <2> PICK self \in ByzSenders : CByzStep(self)
    BY <1>2
  <2>y. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
          Msgs' = Msgs \cup {y}
    BY DEF CByzStep
  <2>ns. Sig(y) \notin SafeAcceptors
    BY <2>y DEF ByzSenders
  <2>new. \A m \in Msgs' : Sig(m) \in SafeAcceptors => m.priors = Refs(m)
    <3> SUFFICES ASSUME NEW m \in Msgs', Sig(m) \in SafeAcceptors
        PROVE m.priors = Refs(m)
      OBVIOUS
    <3>a. CASE m \in Msgs
      BY <3>a DEF CSafeSentCanonical
    <3>b. CASE m = y
      BY <3>b, <2>ns
    <3> QED BY <2>y, <3>a, <3>b
  <2> QED BY <2>new DEF CSafeSentCanonical
<1>3. CASE UNCHANGED CVars
  <2>1. Msgs' = Msgs
    BY <1>3 DEF CVars
  <2> QED BY <2>1, CSafeSentCanonical DEF CSafeSentCanonical
<1> QED BY <1>1, <1>2, <1>3 DEF CNext
=============================================================================
