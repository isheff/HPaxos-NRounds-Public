---------------------------- MODULE BridgeUncaught ----------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* A SafeAcceptor is never in CaughtS(Msgs), given the uncaught invariant.
\* INV1 with Spec in the GOAL.
LEMMA BridgeUncaught ==
  ASSUME NEW s, s \in SafeAcceptors
  PROVE  Spec => [](SafeAcceptorsUncaughtInvariant => ~(s \in CaughtS(Msgs)))
<1>1. Init => (SafeAcceptorsUncaughtInvariant => ~(s \in CaughtS(Msgs)))
  BY DEF SafeAcceptorsUncaughtInvariant
<1>2. (SafeAcceptorsUncaughtInvariant => ~(s \in CaughtS(Msgs))) /\ [Next]_vars
        => (SafeAcceptorsUncaughtInvariant => ~(s \in CaughtS(Msgs)))'
  BY DEF SafeAcceptorsUncaughtInvariant
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
