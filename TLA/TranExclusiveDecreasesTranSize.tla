----------------- MODULE TranExclusiveDecreasesTranSize -----------------
\*   MessageInterface  -> TranTrans, TranFinite, TranAcyclic, Messages,
\*                        TranExclusive, Tran (statement)
\*   FiniteSetTheorems -> FS_Subset, FS_CardinalityType (proof)
EXTENDS MessageInterface, FiniteSetTheorems

LEMMA TranExclusiveDecreasesTranSize ==
    ASSUME TranTrans, TranFinite, TranAcyclic,
           NEW m \in Messages,
           NEW x \in TranExclusive(m)
    PROVE Cardinality(Tran(m)) > Cardinality(Tran(x))
<1>1. x \in Tran(m) /\ x # m  BY DEF TranExclusive
<1>2. Tran(x) \subseteq Tran(m)  BY <1>1 DEF TranTrans
<1>3. IsFiniteSet(Tran(m))  BY DEF TranFinite
<1>4. m \in Tran(m)  BY DEF Tran
<1>5. m \notin Tran(x)  BY <1>1 DEF TranAcyclic
<1>6. Tran(m) # Tran(x)  BY <1>4, <1>5
<1>7. Cardinality(Tran(x)) <= Cardinality(Tran(m))  BY <1>2, <1>3, FS_Subset
<1>8. Cardinality(Tran(m)) # Cardinality(Tran(x))  BY <1>2, <1>3, <1>6, FS_Subset
<1>9. Cardinality(Tran(x)) \in Nat /\ Cardinality(Tran(m)) \in Nat
    BY <1>2, <1>3, FS_Subset, FS_CardinalityType
<1> QED BY <1>7, <1>8, <1>9
====================================================================
