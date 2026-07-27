----------------------------- MODULE BoxKnownEq -----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

LEMMA BoxKnownEq == ASSUME NEW p, NEW a, p[1] = a PROVE BKEop(p, a)
<1> USE DEF BKEop
<1>1. Init => (p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a])  OBVIOUS
<1>2. (p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a]) /\ [Next]_vars
        => (p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a])'  OBVIOUS
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
