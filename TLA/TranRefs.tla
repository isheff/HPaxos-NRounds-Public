----------------------------- MODULE TranRefs -----------------------------
\*   FiniteSetTheorems -> FS_Subset
\*   TranSubMessages, TranMaxExists, TranExclusiveDecreasesTranSize,
\*   TranCardNat       -> cited lemmas
\*   TLAPS             -> SMT; proof-only
EXTENDS MessageInterface, FiniteSetTheorems,
        TranSubMessages, TranMaxExists,
        TranExclusiveDecreasesTranSize, TranCardNat
LOCAL INSTANCE TLAPS

THEOREM TranRefs ==
    ASSUME TypeOKMessageInterface, TranFinite, TranTrans, TranAcyclic,
           NEW m \in Messages
    PROVE Tran(m) = {m} \cup UNION {Tran(r) : r \in Refs(m)}
<1>fin. IsFiniteSet(Tran(m))  BY DEF TranFinite
<1>subM. Tran(m) \subseteq Messages  BY TranSubMessages
\* (superset) RHS \subseteq Tran(m)
<1>sup. {m} \cup UNION {Tran(r) : r \in Refs(m)} \subseteq Tran(m)
  <2>1. m \in Tran(m)  BY DEF Tran
  <2>2. ASSUME NEW r \in Refs(m) PROVE Tran(r) \subseteq Tran(m)
    <3>1. r \in TranExclusive(m)  BY <2>2 DEF Refs
    <3>2. r \in Tran(m)  BY <3>1 DEF TranExclusive
    <3> QED BY <3>2 DEF TranTrans
  <2> QED BY <2>1, <2>2
\* (subset) Tran(m) \subseteq RHS
<1>sub. Tran(m) \subseteq {m} \cup UNION {Tran(r) : r \in Refs(m)}
  <2> SUFFICES ASSUME NEW z \in Tran(m), z # m
               PROVE  z \in UNION {Tran(r) : r \in Refs(m)}
    OBVIOUS
  <2>z. z \in TranExclusive(m)  BY DEF TranExclusive
  <2> DEFINE Sz == {y \in TranExclusive(m) : z \in Tran(y)}
  <2>ztran. z \in Tran(z)  BY DEF Tran
  <2>zin. z \in Sz  BY <2>z, <2>ztran
  <2>TEsubM. TranExclusive(m) \subseteq Messages  BY <1>subM DEF TranExclusive
  <2>finSz. IsFiniteSet(Sz)
    <3>1. TranExclusive(m) \subseteq Tran(m)  BY DEF TranExclusive
    <3>2. Sz \subseteq Tran(m)  BY <3>1
    <3> QED BY <3>2, <1>fin, FS_Subset
  <2>SzM. Sz \subseteq Messages  BY <2>TEsubM
  <2>max. PICK r \in Sz : \A y \in Sz : Cardinality(Tran(y)) <= Cardinality(Tran(r))
    BY <2>finSz, <2>zin, <2>SzM, TranMaxExists
  <2>rTE. r \in TranExclusive(m)  BY <2>max
  <2>rz. z \in Tran(r)  BY <2>max
  <2>rRefs. r \in Refs(m)
    <3> SUFFICES ASSUME NEW y \in TranExclusive(m), r \in TranExclusive(y)
                 PROVE FALSE
      BY <2>rTE DEF Refs
    <3>yM. y \in Messages  BY <2>TEsubM
    <3>1. r \in Tran(y)  BY DEF TranExclusive
    <3>2. Tran(r) \subseteq Tran(y)  BY <3>yM, <3>1 DEF TranTrans
    <3>3. z \in Tran(y)  BY <2>rz, <3>2
    <3>4. y \in Sz  BY <3>3
    <3>5. Cardinality(Tran(y)) <= Cardinality(Tran(r))  BY <3>4, <2>max
    <3>6. Cardinality(Tran(r)) < Cardinality(Tran(y))  BY <3>yM, TranExclusiveDecreasesTranSize
    <3>7. Cardinality(Tran(y)) \in Nat /\ Cardinality(Tran(r)) \in Nat
      BY <3>yM, <2>rTE, <2>TEsubM, TranCardNat
    <3> QED BY <3>5, <3>6, <3>7, SMT
  <2> QED BY <2>rRefs, <2>rz
<1> QED BY <1>sup, <1>sub
====================================================================
