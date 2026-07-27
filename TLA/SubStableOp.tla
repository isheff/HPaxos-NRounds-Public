----------------------------- MODULE SubStableOp -----------------------------
EXTENDS HPaxosPlusCal, SubsetNetworkStable

LEMMA SubStableOp == ASSUME NEW SS PROVE SubStabOp(SS)  BY SubsetNetworkStable DEF SubStabOp
====================================================================
