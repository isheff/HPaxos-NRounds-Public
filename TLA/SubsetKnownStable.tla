-------------------------- MODULE SubsetKnownStable --------------------------
EXTENDS HPaxosPlusCal, KnownMono, InvHolds
LOCAL INSTANCE TLAPS

LEMMA SubsetKnownStable ==
  ASSUME NEW a \in SafeAcceptors, NEW SS
  PROVE  Spec => [](SS \subseteq known_messages[a] => [](SS \subseteq known_messages[a]))
<1>1. Inv /\ [Next]_vars /\ SS \subseteq known_messages[a] => (SS \subseteq known_messages[a])'  BY KnownMono
<1>2. Spec => []Inv  BY InvHolds
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
