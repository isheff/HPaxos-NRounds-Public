----------------------------- MODULE NetStable -----------------------------
EXTENDS HPaxosPlusCal, NetMono
LOCAL INSTANCE TLAPS

\* Stability: once sent, always sent (Msgs only grows).
\* Bound variable xx is pinned -- SentStableInvariant's chain shares the name,
\* and TLAPS will not alpha-rename a bound variable inside a [].
LEMMA NetStable ==
  ASSUME NEW xx
  PROVE  Spec => [](xx \in Msgs => [](xx \in Msgs))
<1>1. xx \in Msgs /\ [Next]_vars => (xx \in Msgs)'  BY NetMono
<1> QED  BY <1>1, PTL DEF Spec
====================================================================
