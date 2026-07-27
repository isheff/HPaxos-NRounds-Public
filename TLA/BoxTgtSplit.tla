---------------------------- MODULE BoxTgtSplit ----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

LEMMA BoxTgtSplit ==
  ASSUME NEW U, NEW p0, p0 \in U
  PROVE  Spec => [](CP_Tgt(U) <=> (CP_Tgt(U \ {p0}) /\ p0[2] \in known_messages[p0[1]]))
<1>1. Init => (CP_Tgt(U) <=> (CP_Tgt(U \ {p0}) /\ p0[2] \in known_messages[p0[1]]))
  BY DEF CP_Tgt
<1>2. (CP_Tgt(U) <=> (CP_Tgt(U \ {p0}) /\ p0[2] \in known_messages[p0[1]])) /\ [Next]_vars
        => (CP_Tgt(U) <=> (CP_Tgt(U \ {p0}) /\ p0[2] \in known_messages[p0[1]]))'
  BY DEF CP_Tgt
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
