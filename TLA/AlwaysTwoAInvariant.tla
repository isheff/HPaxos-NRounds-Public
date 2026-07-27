------------------------- MODULE AlwaysTwoAInvariant -------------------------
EXTENDS HPaxosPlusCal, TwoAHoldsT, TwoAInvariantEqT
LOCAL INSTANCE TLAPS

THEOREM AlwaysTwoAInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ AcceptorsAssumptions
  )=> []TwoAInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions,
                    AcceptorsAssumptions
             PROVE []TwoAInvariant  OBVIOUS
<1>1. []TwoAInvariantT  BY TwoAHoldsT
<1> QED BY <1>1, TwoAInvariantEqT, PTL
====================================================================
