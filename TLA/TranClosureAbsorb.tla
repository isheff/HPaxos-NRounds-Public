------------------------ MODULE TranClosureAbsorb ------------------------
\* The second set parameter is named Msgs, not S: an earlier version used S
\* and collided with callers' own local S (the bound-variable-collision
\* gotcha), exhausting the backend at the application site.
EXTENDS MessageInterface, TranClosureClosed

LEMMA TranClosureAbsorb ==
  ASSUME TypeOKMessageInterface, TranTrans, NEW mm \in SUBSET Messages, NEW Msgs \in SUBSET Messages,
         Msgs \subseteq TranClosure(mm)
  PROVE TranClosure(Msgs) \subseteq TranClosure(mm)
<1> SUFFICES ASSUME NEW z \in TranClosure(Msgs) PROVE z \in TranClosure(mm)  OBVIOUS
<1>1. PICK x \in Msgs : z \in Tran(x)  BY DEF TranClosure
<1>2. x \in TranClosure(mm)  BY <1>1
<1>3. Tran(x) \subseteq TranClosure(mm)  BY <1>2, TranClosureClosed
<1> QED BY <1>1, <1>3
====================================================================
