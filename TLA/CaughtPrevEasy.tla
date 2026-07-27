-------------------------- MODULE CaughtPrevEasy --------------------------
EXTENDS MessageInterface, PrevDom

\* Easy direction: distinct same-sig m1,m2 sharing a Prev witness (or both
\* having empty Prev) are incomparable.
LEMMA CaughtPrevEasy ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic, NEW a \in Acceptors,
         NEW m1 \in Messages, NEW m2 \in Messages,
         Sig(m1) = a, Sig(m2) = a, m1 # m2,
         (Prev(m1) = {} /\ Prev(m2) = {}) \/ (Prev(m1) \cap Prev(m2) # {})
  PROVE m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
<1>1. CASE Prev(m1) = {} /\ Prev(m2) = {}
  <2>a. m1 \notin Tran(m2)
    <3> SUFFICES ASSUME m1 \in Tran(m2) PROVE FALSE  OBVIOUS
    <3>1. m1 \in TranExclusive(m2)  BY DEF TranExclusive
    <3>2. \E q \in Prev(m2) : m1 \in Tran(q)  BY <3>1, PrevDom
    <3> QED BY <3>2, <1>1
  <2>b. m2 \notin Tran(m1)
    <3> SUFFICES ASSUME m2 \in Tran(m1) PROVE FALSE  OBVIOUS
    <3>1. m2 \in TranExclusive(m1)  BY DEF TranExclusive
    <3>2. \E q \in Prev(m1) : m2 \in Tran(q)  BY <3>1, PrevDom
    <3> QED BY <3>2, <1>1
  <2> QED BY <2>a, <2>b
<1>2. CASE Prev(m1) \cap Prev(m2) # {}
  <2>q. PICK q \in Prev(m1) \cap Prev(m2) : TRUE  BY <1>2
  <2>qm1. q \in Prev(m1)  BY <2>q
  <2>qm2. q \in Prev(m2)  BY <2>q
  <2>a. m1 \notin Tran(m2)
    <3> SUFFICES ASSUME m1 \in Tran(m2) PROVE FALSE  OBVIOUS
    <3>1. q \in TranExclusive(m1) /\ Sig(q) = Sig(m1)  BY <2>qm1 DEF Prev
    <3>2. m1 \in TranExclusive(m2)  BY DEF TranExclusive
    <3>3. \A y \in TranExclusive(m2): q \in TranExclusive(y) => Sig(q) # Sig(y)
      BY <2>qm2 DEF Prev
    <3>4. Sig(q) # Sig(m1)  BY <3>1, <3>2, <3>3
    <3> QED BY <3>1, <3>4
  <2>b. m2 \notin Tran(m1)
    <3> SUFFICES ASSUME m2 \in Tran(m1) PROVE FALSE  OBVIOUS
    <3>1. q \in TranExclusive(m2) /\ Sig(q) = Sig(m2)  BY <2>qm2 DEF Prev
    <3>2. m2 \in TranExclusive(m1)  BY DEF TranExclusive
    <3>3. \A y \in TranExclusive(m1): q \in TranExclusive(y) => Sig(q) # Sig(y)
      BY <2>qm1 DEF Prev
    <3>4. Sig(q) # Sig(m2)  BY <3>1, <3>2, <3>3
    <3> QED BY <3>1, <3>4
  <2> QED BY <2>a, <2>b
<1> QED BY <1>1, <1>2
====================================================================
