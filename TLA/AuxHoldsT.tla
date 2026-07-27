----------------------------- MODULE AuxHoldsT -----------------------------
EXTENDS HPaxosPlusCal, InitAuxT, AuxStepT
LOCAL INSTANCE TLAPS

LEMMA AuxHoldsT == Spec => []AuxT
<1>1. Init => AuxT  BY InitAuxT
<1>2. AuxT /\ [Next]_vars => AuxT'  BY AuxStepT
<1> QED BY <1>1, <1>2, PTL DEF Spec
====================================================================
