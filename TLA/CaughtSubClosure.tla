-------------------------- MODULE CaughtSubClosure --------------------------
EXTENDS MessageInterface, TranClosureClosed

\* Everything caught as of a closure member is caught as of the closure.
LEMMA CaughtSubClosure ==
  ASSUME TypeOKMessageInterface, TranTrans,
         NEW mset \in SUBSET Messages, NEW x \in TranClosure(mset)
  PROVE Caught(x) \subseteq CaughtS(TranClosure(mset))
<1>sub. Tran(x) \subseteq TranClosure(mset)  BY TranClosureClosed
<1> SUFFICES ASSUME NEW a \in Caught(x) PROVE a \in CaughtS(TranClosure(mset))  OBVIOUS
<1>1. PICK m1 \in Tran(x), m2 \in Tran(x) :
        Sig(m1)=a /\ Sig(m2)=a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY DEF Caught, CaughtS
<1>2. m1 \in TranClosure(mset) /\ m2 \in TranClosure(mset)  BY <1>1, <1>sub
<1>3. a \in Acceptors  BY DEF Caught, CaughtS
<1> QED BY <1>1, <1>2, <1>3 DEF CaughtS
====================================================================
