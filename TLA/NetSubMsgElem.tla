---------------------------- MODULE NetSubMsgElem ----------------------------
EXTENDS HPaxosPlusCal, InitInv, InvStep
LOCAL INSTANCE TLAPS

\* [](y in Msgs => y in Messages) for a fixed y, via INV1 on Inv /\ phi.
LEMMA NetSubMsgElem ==
  ASSUME NEW y
  PROVE  Spec => [](y \in Msgs => y \in Messages)
<1>1. Init => (Inv /\ (y \in Msgs => y \in Messages))
  <2> SUFFICES ASSUME Init PROVE Inv /\ (y \in Msgs => y \in Messages)  OBVIOUS
  <2>1. Inv  BY InitInv
  <2>2. Msgs = {}  BY DEF Init
  <2> QED  BY <2>1, <2>2
<1>2. (Inv /\ (y \in Msgs => y \in Messages)) /\ [Next]_vars
        => (Inv /\ (y \in Msgs => y \in Messages))'
  <2> SUFFICES ASSUME Inv, (y \in Msgs => y \in Messages), [Next]_vars
               PROVE  (Inv /\ (y \in Msgs => y \in Messages))'
    OBVIOUS
  <2>ip. Inv'  BY InvStep
  <2>nm. Msgs' \in SUBSET Messages  BY <2>ip DEF Inv
  <2>cp. (y \in Messages)' <=> (y \in Messages)  OBVIOUS
  <2>cn. (y \in Msgs)' <=> (y \in Msgs')  OBVIOUS
  <2>2. (y \in Msgs => y \in Messages)'  BY <2>nm, <2>cp, <2>cn
  <2> QED  BY <2>ip, <2>2
<1>3. Spec => [](Inv /\ (y \in Msgs => y \in Messages))  BY <1>1, <1>2, PTL DEF Spec
<1> QED  BY <1>3, PTL
====================================================================
