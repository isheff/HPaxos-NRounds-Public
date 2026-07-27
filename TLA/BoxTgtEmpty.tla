---------------------------- MODULE BoxTgtEmpty ----------------------------
\* Clean-context helper for the fragile INV1-style boxing (PTL chokes on the
\* heavy context inside ConjPairLeadsTo's induction).
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

LEMMA BoxTgtEmpty == ASSUME NEW U, U = {} PROVE Spec => [](CP_Tgt(U))
<1>1. Init => CP_Tgt(U)  BY DEF CP_Tgt
<1>2. CP_Tgt(U) /\ [Next]_vars => (CP_Tgt(U))'  BY DEF CP_Tgt
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
