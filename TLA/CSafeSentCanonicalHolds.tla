------------------------ MODULE CSafeSentCanonicalHolds ------------------------
\* THE canonicality invariant of HPaxosPlusCalConcrete: every message a safe
\* acceptor has ever sent carries exactly its refs as its priors field.
\* Well-formedness cannot check this (it is not digest-decidable, and byz
\* senders may violate it freely) -- but honest behaviour maintains it.
EXTENDS HPaxosPlusCalConcrete, CJointHolds, CSafeSentCanonicalStep, TLAPS

THEOREM CSafeSentCanonicalHolds ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption
  PROVE  CSpec => [](\A m \in Msgs :
                       Sig(m) \in SafeAcceptors => m.priors = Refs(m))
<1>1. CInit => CSafeSentCanonical
  BY DEF CInit, CSafeSentCanonical
<1>2. CJoint /\ CSafeSentCanonical /\ [CNext]_CVars => CSafeSentCanonical'
  BY CSafeSentCanonicalStep
<1>3. CSpec => []CJoint
  BY CJointHolds
<1>4. CSpec => []CSafeSentCanonical
  BY <1>1, <1>2, <1>3, PTL DEF CSpec
<1>5. CSafeSentCanonical
        <=> (\A m \in Msgs : Sig(m) \in SafeAcceptors => m.priors = Refs(m))
  BY DEF CSafeSentCanonical
<1> QED BY <1>4, <1>5, PTL
=============================================================================
