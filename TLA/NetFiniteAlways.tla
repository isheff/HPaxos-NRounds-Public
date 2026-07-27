--------------------------- MODULE NetFiniteAlways ---------------------------
EXTENDS HPaxosPlusCal, InvHolds
LOCAL INSTANCE TLAPS

LEMMA NetFiniteAlways == Spec => [](IsFiniteSet(Msgs))
<1>1. Spec => []Inv  BY InvHolds
<1> QED  BY <1>1, PTL DEF Inv
====================================================================
