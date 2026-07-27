------------------------------ MODULE PrevDom ------------------------------
\*   FiniteSetTheorems -> FS_Subset
\*   TranSubMessages, TranMaxExists, TranExclusiveDecreasesTranSize,
\*   TranCardNat       -> cited lemmas
\*   TLAPS             -> SMT; proof-only
EXTENDS MessageInterface, FiniteSetTheorems,
        TranSubMessages, TranMaxExists,
        TranExclusiveDecreasesTranSize, TranCardNat
LOCAL INSTANCE TLAPS

\* Same-signature domination: any same-sig strict ancestor is below some Prev.
LEMMA PrevDom ==
  ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic,
         NEW z \in Messages, NEW x \in TranExclusive(z), Sig(x) = Sig(z)
  PROVE \E q \in Prev(z) : x \in Tran(q)
<1> DEFINE U == {y \in TranExclusive(z) : Sig(y) = Sig(z) /\ x \in Tran(y)}
<1>xx. x \in Tran(x)  BY DEF Tran
<1>1. x \in U  BY <1>xx
<1>2. U \subseteq Messages
  <2> SUFFICES ASSUME NEW y \in U PROVE y \in Messages  OBVIOUS
  <2>1. y \in Tran(z)  BY DEF TranExclusive
  <2> QED BY <2>1, TranSubMessages
<1>3. IsFiniteSet(U)
  <2>1. IsFiniteSet(Tran(z))  BY DEF TranFinite
  <2>2. U \subseteq Tran(z)  BY DEF TranExclusive
  <2> QED BY <2>1, <2>2, FS_Subset
<1>4. PICK q \in U : \A y \in U : Cardinality(Tran(y)) <= Cardinality(Tran(q))
  BY <1>1, <1>2, <1>3, TranMaxExists
<1>5. q \in TranExclusive(z) /\ Sig(q) = Sig(z) /\ x \in Tran(q)  BY <1>4
<1>7. q \in Prev(z)
  <2> SUFFICES \A y \in TranExclusive(z): q \in TranExclusive(y) => Sig(q) # Sig(y)
    BY <1>5 DEF Prev
  <2> SUFFICES ASSUME NEW y \in TranExclusive(z), q \in TranExclusive(y), Sig(q) = Sig(y)
               PROVE FALSE  OBVIOUS
  <2>0. q \in Tran(y) /\ q # y  BY DEF TranExclusive
  <2>0b. Sig(y) = Sig(z)  BY <1>5
  <2>1. y \in Messages  BY TranSubMessages DEF TranExclusive
  <2>2. x \in Tran(y)
    <3>1. Tran(q) \subseteq Tran(y)  BY <2>0, <2>1, TranTrans DEF TranTrans
    <3> QED BY <1>5, <3>1
  <2>3. y \in U  BY <2>2, <2>0b
  <2>4. Cardinality(Tran(y)) <= Cardinality(Tran(q))  BY <2>3, <1>4
  <2>6. Cardinality(Tran(q)) < Cardinality(Tran(y))  BY <2>0, <2>1, TranExclusiveDecreasesTranSize
  <2>qm. q \in Messages  BY <1>2, <1>4
  <2>7. Cardinality(Tran(q)) \in Nat /\ Cardinality(Tran(y)) \in Nat  BY <2>qm, <2>1, TranCardNat
  <2> QED BY <2>4, <2>6, <2>7, SMT
<1> QED BY <1>5, <1>7
====================================================================
