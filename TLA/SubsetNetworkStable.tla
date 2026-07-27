------------------------- MODULE SubsetNetworkStable -------------------------
EXTENDS HPaxosPlusCal, NetMono
LOCAL INSTANCE TLAPS

\* Bound variable SS is pinned to match SentStableInvariant's chain.
LEMMA SubsetNetworkStable ==
  ASSUME NEW SS
  PROVE  Spec => [](SS \subseteq Msgs => [](SS \subseteq Msgs))
<1>1. SS \subseteq Msgs /\ [Next]_vars => (SS \subseteq Msgs)'  BY NetMono
<1> QED  BY <1>1, PTL DEF Spec
====================================================================
