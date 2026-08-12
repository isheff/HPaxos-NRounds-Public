----------------------------- MODULE MaxDominated -----------------------------
\*   MaxProps -> cited lemma (brings FiniteSetsExt's Max)
\*   FiniteSetTheorems -> FS_Subset
EXTENDS MaxProps, FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* Max is decided by any dominating subset: if D \subseteq A and every
\* element of A is bounded by some element of D, the two maxima agree.
LEMMA MaxDominated ==
  ASSUME NEW A, NEW D, IsFiniteSet(A), A # {}, \A a \in A : a \in Nat,
         D \subseteq A, \A a \in A : \E d \in D : a <= d
  PROVE Max(A) = Max(D)
<1>fd. IsFiniteSet(D)  BY FS_Subset
<1>dn. \A d \in D : d \in Nat  OBVIOUS
<1>ne. D # {}
  <2>1. PICK a \in A : TRUE  OBVIOUS
  <2>2. PICK d \in D : a <= d  OBVIOUS
  <2> QED BY <2>2
<1>ma. Max(A) \in A /\ \A y \in A : Max(A) >= y  BY MaxProps
<1>md. Max(D) \in D /\ \A y \in D : Max(D) >= y  BY <1>fd, <1>dn, <1>ne, MaxProps
<1>1. Max(A) >= Max(D)  BY <1>ma, <1>md
<1>2. PICK d \in D : Max(A) <= d  BY <1>ma
<1>3. Max(D) >= d  BY <1>2, <1>md
<1>nat. Max(A) \in Nat /\ Max(D) \in Nat /\ d \in Nat
  BY <1>ma, <1>md, <1>2, <1>dn
<1> QED BY <1>1, <1>2, <1>3, <1>nat, SMT
=============================================================================
