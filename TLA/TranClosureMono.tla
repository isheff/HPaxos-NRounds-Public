--------------------------- MODULE TranClosureMono ---------------------------
EXTENDS HPaxosPlusCal

LEMMA TranClosureMono ==
  ASSUME NEW m \in SUBSET Messages, NEW mp \in SUBSET Messages, m \subseteq mp
  PROVE TranClosure(m) \subseteq TranClosure(mp)
<1> SUFFICES ASSUME NEW z \in TranClosure(m) PROVE z \in TranClosure(mp)  OBVIOUS
<1>1. PICK x \in m : z \in Tran(x)  BY DEF TranClosure
<1>2. x \in mp  BY <1>1
<1> QED BY <1>1, <1>2 DEF TranClosure
====================================================================
