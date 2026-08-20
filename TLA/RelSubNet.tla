----------------------------- MODULE RelSubNet -----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* RelevantMsgs is a subset of Msgs, boxed (definitional).
LEMMA RelSubNet == ASSUME NEW m PROVE RelSubNetOp(m)
<1> USE DEF RelSubNetOp
<1>1. Init => (m \subseteq RelevantMsgs => m \subseteq Msgs)
  BY DEF RelevantMsgs
<1>2. (m \subseteq RelevantMsgs => m \subseteq Msgs) /\ [Next]_vars
        => (m \subseteq RelevantMsgs => m \subseteq Msgs)'
  BY DEF RelevantMsgs
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
