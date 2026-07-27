---------------------------- MODULE BoxTranClosed ----------------------------
EXTENDS HPaxosPlusCal, InvHolds
LOCAL INSTANCE TLAPS

LEMMA BoxTranClosed ==
  ASSUME NEW xx \in Messages, NEW w, w \in TranExclusive(xx)
  PROVE  BTCop(xx, w)
<1> USE DEF BTCop
<1>1. Inv /\ {xx} \subseteq Msgs => w \in Msgs  BY DEF Inv
<1>2. Spec => []Inv  BY InvHolds
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
