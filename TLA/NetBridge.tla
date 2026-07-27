----------------------------- MODULE NetBridge -----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

LEMMA NetBridge == ASSUME NEW xx PROVE NBop(xx)
<1> USE DEF NBop
<1>1. Init => (({xx} \subseteq Msgs) <=> (xx \in Msgs))  OBVIOUS
<1>2. (({xx} \subseteq Msgs) <=> (xx \in Msgs)) /\ [Next]_vars
        => (({xx} \subseteq Msgs) <=> (xx \in Msgs))'  OBVIOUS
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
