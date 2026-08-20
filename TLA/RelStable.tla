----------------------------- MODULE RelStable -----------------------------
EXTENDS HPaxosPlusCal, RelMono, InvHolds
LOCAL INSTANCE TLAPS

\* Stability: once live-relevant and sent, always so.  Bound variable xx
\* pinned as in NetStable.
LEMMA RelStable ==
  ASSUME AcceptorsAssumptions, NEW xx
  PROVE  RelStableOp(xx)
<1> USE DEF RelStableOp
<1>step. Inv /\ (xx \in RelevantMsgs) /\ [Next]_vars => (xx \in RelevantMsgs)'
  BY RelMono
<1>inv. Spec => []Inv  BY InvHolds
<1> QED  BY <1>step, <1>inv, PTL DEF Spec
====================================================================
