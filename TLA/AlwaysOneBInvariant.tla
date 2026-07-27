------------------------- MODULE AlwaysOneBInvariant -------------------------
EXTENDS HPaxosPlusCal, OneBHoldsT, OneBInvariantEqT
LOCAL INSTANCE TLAPS

THEOREM AlwaysOneBInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ AcceptorsAssumptions
  )=> []OneBInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions,
                    AcceptorsAssumptions
             PROVE []OneBInvariant  OBVIOUS
<1>1. []OneBInvariantT  BY OneBHoldsT
<1> QED BY <1>1, OneBInvariantEqT, PTL
====================================================================
