---------------------- MODULE TranClosureIdempotent ----------------------
EXTENDS MessageInterface, TranClosureClosed,
        TranClosureAbsorb, TranClosureExpanding

LEMMA TranClosureIdempotent ==
  ASSUME TypeOKMessageInterface, TranTrans, NEW mm \in SUBSET Messages
  PROVE TranClosure(TranClosure(mm)) = TranClosure(mm)
<1>tcmsgs. TranClosure(mm) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in TranClosure(mm) PROVE z \in Messages  OBVIOUS
  <2> QED BY TranClosureClosed
<1>sub. TranClosure(TranClosure(mm)) \subseteq TranClosure(mm)
  <2>1. TranClosure(mm) \subseteq TranClosure(mm)  OBVIOUS
  <2> QED BY <2>1, <1>tcmsgs, TranClosureAbsorb
<1>sup. TranClosure(mm) \subseteq TranClosure(TranClosure(mm))  BY TranClosureExpanding
<1> QED BY <1>sub, <1>sup
====================================================================
