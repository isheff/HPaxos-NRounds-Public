--------------------------- MODULE LearnLeadsToW ---------------------------
EXTENDS HPaxosPlusCal, LearnLeadsTo

LEMMA LearnLeadsToW == ASSUME AcceptorsAssumptions, NEW a \in LiveAcceptors, NEW x \in Messages PROVE LLTop(a, x)
BY LearnLeadsTo DEF LLTop
====================================================================
