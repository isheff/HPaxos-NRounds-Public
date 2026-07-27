----------------------------- MODULE OneBHoldsT -----------------------------
EXTENDS HPaxosPlusCal, InitOneBT, OneBStepT, AuxHoldsT
LOCAL INSTANCE TLAPS

LEMMA OneBHoldsT ==
  (Spec /\ MessageInterfaceAssumptions /\ LearnerGraphAssumptions /\ AcceptorsAssumptions) => []OneBInvariantT
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions
             PROVE Spec => []OneBInvariantT  OBVIOUS
<1>1. Init => OneBInvariantT  BY InitOneBT
<1>2. AuxT /\ OneBInvariantT /\ [Next]_vars => OneBInvariantT'
  BY OneBStepT, MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions DEF AuxT
<1>3. Spec => []AuxT  BY AuxHoldsT
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, AuxT
====================================================================
