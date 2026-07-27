------------------------- MODULE CaughtMonotoneTran -------------------------
EXTENDS MessageInterface

\* Catching is monotone along Tran: an ancestor's evidence is a subset of
\* the descendant's evidence.
LEMMA CaughtMonotoneTran ==
  ASSUME TypeOKMessageInterface, TranTrans,
         NEW x \in Messages, NEW y \in Tran(x)
  PROVE Caught(y) \subseteq Caught(x)
<1>sub. Tran(y) \subseteq Tran(x)  BY DEF TranTrans
<1> SUFFICES ASSUME NEW a \in Caught(y) PROVE a \in Caught(x)  OBVIOUS
<1>1. PICK m1 \in Tran(y), m2 \in Tran(y) :
        Sig(m1)=a /\ Sig(m2)=a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY DEF Caught, CaughtS
<1>2. m1 \in Tran(x) /\ m2 \in Tran(x)  BY <1>1, <1>sub
<1>3. a \in Acceptors  BY DEF Caught, CaughtS
<1> QED BY <1>1, <1>2, <1>3 DEF Caught, CaughtS
====================================================================
