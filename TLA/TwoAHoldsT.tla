------------------------------ MODULE TwoAHoldsT ------------------------------
EXTENDS HPaxosPlusCal, InitTwoAT, TwoAStepT, AuxHoldsT
LOCAL INSTANCE TLAPS

LEMMA TwoAHoldsT ==
  (Spec /\ MessageInterfaceAssumptions /\ LearnerGraphAssumptions /\ AcceptorsAssumptions) => []TwoAInvariantT
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions
             PROVE Spec => []TwoAInvariantT  OBVIOUS
<1>1. Init => TwoAInvariantT  BY InitTwoAT
<1>2. AuxT /\ TwoAInvariantT /\ [Next]_vars => TwoAInvariantT'
  BY TwoAStepT, MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions DEF AuxT
<1>3. Spec => []AuxT  BY AuxHoldsT
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec, AuxT
====================================================================
