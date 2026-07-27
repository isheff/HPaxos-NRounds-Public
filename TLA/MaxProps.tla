--------------------------- MODULE MaxProps ---------------------------
\* Both by EXTENDS, so that the FiniteSets/Integers they have in common stays
\* ONE shared copy. Pulling FiniteSetHasMax in by LOCAL INSTANCE instead gives
\* a second copy of IsFiniteSet (renamed IsFiniteSet_1), and the citation of
\* FiniteSetHasMax below then fails to match.
\*   FiniteSetsExt    -> Max (the subject of the lemma), IsFiniteSet, Nat
\*   FiniteSetHasMax  -> the cited lemma
EXTENDS FiniteSetsExt, FiniteSetHasMax

LEMMA MaxProps ==
  ASSUME NEW D, IsFiniteSet(D), D # {}, \A x \in D : x \in Nat
  PROVE Max(D) \in D /\ (\A y \in D : Max(D) >= y)
<1>ex. \E r \in D : \A y \in D : y <= r  BY FiniteSetHasMax
<1> PICK r \in D : \A y \in D : y <= r  BY <1>ex
<1>witness. \E x \in D : \A y \in D : x >= y  OBVIOUS
<1> QED BY <1>witness DEF Max
====================================================================
