---------------------------- MODULE BoxMemInRel ----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* Membership bridge for RelevantMsgs, mirroring BoxMemInNet/BMNop.
LEMMA BoxMemInRel == ASSUME NEW m, NEW x, x \in m PROVE BMNRop(m, x)
<1> USE DEF BMNRop
<1>1. Init => (m \subseteq RelevantMsgs => x \in RelevantMsgs)  OBVIOUS
<1>2. (m \subseteq RelevantMsgs => x \in RelevantMsgs) /\ [Next]_vars
        => (m \subseteq RelevantMsgs => x \in RelevantMsgs)'  OBVIOUS
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
