-------------------------- MODULE KnowLeadsToTranW --------------------------
EXTENDS HPaxosPlusCal, KnowLeadsToTran

LEMMA KnowLeadsToTranW ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         NEW pp \in Messages,
         NEW a \in LiveAcceptors, NEW x \in Messages, x \in Tran(pp)
  PROVE  KLTT(pp, a, x)
BY KnowLeadsToTran DEF KLTT
====================================================================
