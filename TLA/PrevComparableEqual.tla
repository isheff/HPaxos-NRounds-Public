------------------------ MODULE PrevComparableEqual ------------------------
EXTENDS MessageInterface

\* Weaker, well-formedness-free substitute for "Prev has at most one element":
\* two elements of the SAME Prev(m) that happen to be comparable (one in the
\* other's Tran) must be equal, directly from Prev's own maximality clause.
LEMMA PrevComparableEqual ==
  ASSUME NEW m \in Messages,
         NEW x1 \in Prev(m), NEW x2 \in Prev(m), x1 \in Tran(x2)
  PROVE x1 = x2
<1> SUFFICES ASSUME x1 # x2 PROVE FALSE  OBVIOUS
<1>1. x1 \in TranExclusive(m) /\ Sig(x1) = Sig(m)
      /\ \A y \in TranExclusive(m): x1 \in TranExclusive(y) => Sig(x1) # Sig(y)  BY DEF Prev
<1>2. x2 \in TranExclusive(m) /\ Sig(x2) = Sig(m)  BY DEF Prev
<1>3. x1 \in TranExclusive(x2)  BY DEF TranExclusive
<1>4. Sig(x1) # Sig(x2)  BY <1>1, <1>2, <1>3
<1> QED BY <1>1, <1>2, <1>4
====================================================================
