--------------------------- MODULE TranCardNat ---------------------------
\*   MessageInterface   -> TranFinite, Messages, Tran (statement)
\*   FiniteSetTheorems  -> FS_CardinalityType (proof), and it shares the same
\*                         FiniteSets/Integers base MessageInterface already
\*                         carries, so it must be EXTENDS, not INSTANCE.
EXTENDS MessageInterface, FiniteSetTheorems

\* The transitive closure of any message is a finite set with a Nat cardinality.
LEMMA TranCardNat ==
    ASSUME TranFinite, NEW x \in Messages
    PROVE  /\ IsFiniteSet(Tran(x))
           /\ Cardinality(Tran(x)) \in Nat
<1>1. IsFiniteSet(Tran(x))  BY DEF TranFinite
<1> QED BY <1>1, FS_CardinalityType
====================================================================
