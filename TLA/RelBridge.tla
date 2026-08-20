----------------------------- MODULE RelBridge -----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* Singleton bridge for RelevantMsgs, mirroring NetBridge/NBop.
LEMMA RelBridge == ASSUME NEW xx PROVE NBRop(xx)
<1> USE DEF NBRop
<1>1. Init => (({xx} \subseteq RelevantMsgs) <=> (xx \in RelevantMsgs))  OBVIOUS
<1>2. (({xx} \subseteq RelevantMsgs) <=> (xx \in RelevantMsgs)) /\ [Next]_vars
        => (({xx} \subseteq RelevantMsgs) <=> (xx \in RelevantMsgs))'  OBVIOUS
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
