---------------------- MODULE AlwaysAgreementInvariant ----------------------
\* The safety result for the network model: agreement holds at every instant.
EXTENDS HPaxosPlusCal,
        InvHolds, AlwaysSafeAcceptorsUncaughtInvariant, AgreementFromSafeUncaught
LOCAL INSTANCE TLAPS

THEOREM AlwaysAgreementInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
  )=> []AgreementInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions
             PROVE []AgreementInvariant
  OBVIOUS
<1>1. []Inv  BY InvHolds
<1>2. []SafeAcceptorsUncaughtInvariant  BY AlwaysSafeAcceptorsUncaughtInvariant
<1> QED BY <1>1, <1>2, AgreementFromSafeUncaught, PTL
====================================================================
