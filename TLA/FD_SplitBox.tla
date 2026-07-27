----------------------------- MODULE FD_SplitBox -----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

LEMMA FD_SplitBox ==
  ASSUME NEW U, NEW p0, p0 \in U
  PROVE  Spec => [](FD_Tgt(U) <=> (FD_Tgt(U \ {p0}) /\ p0 \in Msgs))
<1>1. Init => (FD_Tgt(U) <=> (FD_Tgt(U \ {p0}) /\ p0 \in Msgs))  BY DEF FD_Tgt
<1>2. (FD_Tgt(U) <=> (FD_Tgt(U \ {p0}) /\ p0 \in Msgs)) /\ [Next]_vars
        => (FD_Tgt(U) <=> (FD_Tgt(U \ {p0}) /\ p0 \in Msgs))'  BY DEF FD_Tgt
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
