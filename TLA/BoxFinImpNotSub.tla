--------------------------- MODULE BoxFinImpNotSub ---------------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems
LOCAL INSTANCE TLAPS

LEMMA BoxFinImpNotSub ==
  ASSUME NEW m, ~IsFiniteSet(m)
  PROVE  Spec => [](IsFiniteSet(Msgs) => ~(m \subseteq Msgs))
<1>1. Init => (IsFiniteSet(Msgs) => ~(m \subseteq Msgs))  BY FS_Subset
<1>2. (IsFiniteSet(Msgs) => ~(m \subseteq Msgs)) /\ [Next]_vars
        => (IsFiniteSet(Msgs) => ~(m \subseteq Msgs))'  BY FS_Subset
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
