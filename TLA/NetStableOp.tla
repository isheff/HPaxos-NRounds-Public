----------------------------- MODULE NetStableOp -----------------------------
EXTENDS HPaxosPlusCal, NetStable

LEMMA NetStableOp == ASSUME NEW xx PROVE ElStabOp(xx)  BY NetStable DEF ElStabOp
====================================================================
