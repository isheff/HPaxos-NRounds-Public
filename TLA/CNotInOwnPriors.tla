--------------------------- MODULE CNotInOwnPriors ---------------------------
\* A message is never among its own priors: CFilterOut pins priors to CRefs,
\* which lives inside the STRICT history.
EXTENDS HPaxosPlusCalConcrete, CFields, CMessagesSubMC, CSelfInTran, TLAPS

LEMMA CNotInOwnPriors ==
  ASSUME ConcreteMessageInterface, NEW x \in Messages
  PROVE  x \notin x.priors
<1>cmi. MessageInterface = CMI
  BY DEF ConcreteMessageInterface
<1>msg. Messages = CMessages
  BY <1>cmi, CFields
<1>mc. x \in CMC
  BY <1>msg, CMessagesSubMC
<1>1. x \in CTran(x)
  BY <1>mc, CSelfInTran
<1>2. CWellFormed(x)
  BY <1>cmi, <1>msg, <1>1 DEF CMessages
<1>3. x.priors = CRefs(x)
  BY <1>2 DEF CWellFormed, CFilterOut
<1> QED
  BY <1>3 DEF CRefs, CTranExcl
=============================================================================
