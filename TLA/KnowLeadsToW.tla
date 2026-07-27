--------------------------- MODULE KnowLeadsToW ---------------------------
EXTENDS HPaxosPlusCal, KnowLeadsTo

LEMMA KnowLeadsToW ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         NEW a \in LiveAcceptors, NEW x \in Messages
  PROVE  KLT(a, x)
BY KnowLeadsTo DEF KLT
====================================================================
