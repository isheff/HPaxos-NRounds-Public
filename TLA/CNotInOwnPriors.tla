--------------------------- MODULE CNotInOwnPriors ---------------------------
\* A message is never among its own priors.  This needs no canonicality:
\* priors live at strictly lower construction levels (CPriorsDecreasesLevel),
\* so x \in x.priors would put x's level strictly below itself.
EXTENDS HPaxosPlusCalConcrete, CFields, CMessagesSubMC, CPriorsDecreasesLevel,
        CMinLevelDom, TLAPS

LEMMA CNotInOwnPriors ==
  ASSUME ConcreteMessageInterface, NEW x \in Messages
  PROVE  x \notin x.priors
<1>cmi. MessageInterface = CMI
  BY DEF ConcreteMessageInterface
<1>msg. Messages = CMessages
  BY <1>cmi, CFields
<1>mc. x \in CMC
  BY <1>msg, CMessagesSubMC
<1>1. CASE x \in x.priors
  <2>1. x \in CPriors(x)
    BY <1>1 DEF CPriors
  <2>2. CMinLevel(x) < CMinLevel(x)
    BY <1>mc, <2>1, CPriorsDecreasesLevel
  <2>3. CMinLevel(x) \in Nat
    BY <1>mc, CMinLevelDom
  <2> QED
    BY <2>2, <2>3
<1> QED
  BY <1>1
=============================================================================
