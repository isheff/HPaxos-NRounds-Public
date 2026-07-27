----------------------------- MODULE KnownSubNet -----------------------------
EXTENDS HPaxosPlusCal, InitInv, InvStep
LOCAL INSTANCE TLAPS

LEMMA KnownSubNet ==
  ASSUME NEW s \in SafeAcceptors
  PROVE  Spec => KnownNetBoxOp(s)
<1>1. Init => (Inv /\ (\A xx : xx \in known_messages[s] => xx \in Msgs))
  <2> SUFFICES ASSUME Init PROVE Inv /\ (\A xx : xx \in known_messages[s] => xx \in Msgs)  OBVIOUS
  <2>1. Inv  BY InitInv
  <2>2. \A xx : xx \in known_messages[s] => xx \in Msgs  BY <2>1 DEF Inv
  <2> QED  BY <2>1, <2>2
<1>2. (Inv /\ (\A xx : xx \in known_messages[s] => xx \in Msgs)) /\ [Next]_vars
        => (Inv /\ (\A xx : xx \in known_messages[s] => xx \in Msgs))'
  <2> SUFFICES ASSUME Inv, (\A xx : xx \in known_messages[s] => xx \in Msgs), [Next]_vars
               PROVE  (Inv /\ (\A xx : xx \in known_messages[s] => xx \in Msgs))'
    OBVIOUS
  <2>ip. Inv'  BY InvStep
  <2>2. (\A xx : xx \in known_messages[s] => xx \in Msgs)'  BY <2>ip DEF Inv
  <2> QED  BY <2>ip, <2>2
<1>3. Spec => [](Inv /\ (\A xx : xx \in known_messages[s] => xx \in Msgs))  BY <1>1, <1>2, PTL DEF Spec
<1> QED  BY <1>3, PTL DEF KnownNetBoxOp
====================================================================
