---------------- MODULE AlwaysSafeAcceptorsUncaughtInvariant ----------------
EXTENDS HPaxosPlusCal, ChainHolds, ChainImpliesUncaught
LOCAL INSTANCE TLAPS

LEMMA AlwaysSafeAcceptorsUncaughtInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
  )=> []SafeAcceptorsUncaughtInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions
             PROVE []SafeAcceptorsUncaughtInvariant
  OBVIOUS
<1>chain. Spec => []SafeAcceptorChainInv  BY ChainHolds
<1> QED BY <1>chain, ChainImpliesUncaught, PTL
====================================================================
