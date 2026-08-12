------------------------- MODULE BalFldMaxExists -------------------------
\*   FiniteSetTheorems -> FS_Image
\*   FiniteSetHasMax   -> cited lemma
\*   TLAPS             -> proof-only
EXTENDS FiniteSetTheorems, FiniteSetHasMax
LOCAL INSTANCE TLAPS

\* Named projection so FS_Image can match the image set by operator name.
BalFld1(c) == c.bal

\* A finite, non-empty set of records whose bal fields are naturals has a
\* member with maximal bal. (Mirrors PairFstMaxExists for .bal.)
LEMMA BalFldMaxExists ==
  ASSUME NEW C, IsFiniteSet(C), C # {}, \A c \in C : c.bal \in Nat
  PROVE \E c \in C : \A c2 \in C : c.bal >= c2.bal
<1> DEFINE F == {BalFld1(c) : c \in C}
<1>fin. IsFiniteSet(F)  BY FS_Image
<1>ne. F # {}  OBVIOUS
<1>nat. \A v \in F : v \in Nat  BY DEF BalFld1
<1>mx. PICK r \in F : \A v \in F : v <= r  BY <1>fin, <1>ne, <1>nat, FiniteSetHasMax
<1>c. PICK c \in C : BalFld1(c) = r  BY <1>mx
<1>all. \A c2 \in C : c2.bal <= c.bal
  <2> SUFFICES ASSUME NEW c2 \in C PROVE c2.bal <= c.bal  OBVIOUS
  <2>1. BalFld1(c2) \in F  OBVIOUS
  <2>2. BalFld1(c2) <= r  BY <2>1, <1>mx
  <2> QED BY <2>2, <1>c DEF BalFld1
<1> QED BY <1>c, <1>all
====================================================================
