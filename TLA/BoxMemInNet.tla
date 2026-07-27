---------------------------- MODULE BoxMemInNet ----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

LEMMA BoxMemInNet == ASSUME NEW m, NEW x, x \in m PROVE BMNop(m, x)
<1> USE DEF BMNop
<1>1. Init => (m \subseteq Msgs => x \in Msgs)  OBVIOUS
<1>2. (m \subseteq Msgs => x \in Msgs) /\ [Next]_vars
        => (m \subseteq Msgs => x \in Msgs)'  OBVIOUS
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
