-------------------------- MODULE KnownStablePair --------------------------
EXTENDS HPaxosPlusCal, KnownMono, InvHolds
LOCAL INSTANCE TLAPS

LEMMA KnownStablePair ==
  ASSUME NEW p0 \in SafeAcceptors \X Messages
  PROVE  Spec => [](p0[2] \in known_messages[p0[1]] => [](p0[2] \in known_messages[p0[1]]))
<1>1. p0[1] \in SafeAcceptors  OBVIOUS
<1>2. Inv /\ [Next]_vars /\ p0[2] \in known_messages[p0[1]]
        => (p0[2] \in known_messages[p0[1]])'
  BY KnownMono, <1>1
<1>3. Spec => []Inv  BY InvHolds
<1> QED  BY <1>2, <1>3, PTL DEF Spec
====================================================================
