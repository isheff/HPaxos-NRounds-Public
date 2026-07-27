------------------------- MODULE TranClosureUnion -------------------------
EXTENDS MessageInterface

LEMMA TranClosureUnion ==
  ASSUME NEW A, NEW C
  PROVE TranClosure(A \cup C) = TranClosure(A) \cup TranClosure(C)
BY DEF TranClosure
====================================================================
