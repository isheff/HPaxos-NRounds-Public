------------------------- MODULE TranClosureClosed -------------------------
EXTENDS MessageInterface, TranSubMessages

\* TranClosure is Tran-closed and stays inside Messages.
LEMMA TranClosureClosed ==
  ASSUME TypeOKMessageInterface, TranTrans,
         NEW mset \in SUBSET Messages, NEW x \in TranClosure(mset)
  PROVE x \in Messages /\ Tran(x) \subseteq TranClosure(mset)
<1>1. PICK y \in mset : x \in Tran(y)  BY DEF TranClosure
<1>2. y \in Messages  BY <1>1
<1>3. x \in Messages  BY <1>1, <1>2, TranSubMessages
<1>4. Tran(x) \subseteq Tran(y)  BY <1>1, <1>2 DEF TranTrans
<1>5. Tran(y) \subseteq TranClosure(mset)  BY <1>1 DEF TranClosure
<1> QED BY <1>3, <1>4, <1>5
====================================================================
