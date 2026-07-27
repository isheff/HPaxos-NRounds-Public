----------------------------- MODULE InvHolds -----------------------------
\* TLAPS supplies PTL. It declares no colliding operators, so LOCAL INSTANCE
\* is safe here (same as elsewhere in split/).
EXTENDS HPaxosPlusCal, InitInv, InvStep
LOCAL INSTANCE TLAPS

LEMMA InvHolds == Spec => []Inv
<1>1. Init => Inv  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'  BY InvStep
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
