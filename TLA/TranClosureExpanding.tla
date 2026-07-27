----------------------- MODULE TranClosureExpanding -----------------------
EXTENDS MessageInterface

LEMMA TranClosureExpanding == ASSUME NEW S PROVE S \subseteq TranClosure(S)
<1> SUFFICES ASSUME NEW x \in S PROVE x \in TranClosure(S)  OBVIOUS
<1>1. x \in Tran(x)  BY DEF Tran
<1> QED BY <1>1 DEF TranClosure
====================================================================
