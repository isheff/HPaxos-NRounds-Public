------------------------- MODULE LearnLeadsToTranW -------------------------
EXTENDS HPaxosPlusCal, LearnLeadsToTran

LEMMA LearnLeadsToTranW ==
  ASSUME AcceptorsAssumptions, NEW pp,
         NEW a \in LiveAcceptors, NEW x \in Messages, x \in Tran(pp)
  PROVE  LLTTop(pp, a, x)
BY LearnLeadsToTran DEF LLTTop
====================================================================
