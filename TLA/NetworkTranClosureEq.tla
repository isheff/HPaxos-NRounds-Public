------------------------- MODULE NetworkTranClosureEq -------------------------
EXTENDS HPaxosPlusCal

LEMMA NetworkTranClosureEq ==
  ASSUME Inv
  PROVE TranClosure(Msgs) = Msgs
<1>sub1. Msgs \subseteq TranClosure(Msgs)
  BY DEF TranClosure, Tran
<1>sub2. TranClosure(Msgs) \subseteq Msgs
  <2> SUFFICES ASSUME NEW z \in TranClosure(Msgs) PROVE z \in Msgs
    BY DEF TranClosure
  <2>1. PICK y \in Msgs : z \in Tran(y)  BY DEF TranClosure
  <2>2. z = y \/ z \in TranExclusive(y)  BY <2>1 DEF Tran, TranExclusive
  <2>3. TranExclusive(y) \subseteq Msgs  BY <2>1 DEF Inv
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>sub1, <1>sub2
====================================================================
