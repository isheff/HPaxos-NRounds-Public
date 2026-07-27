-------------------------- MODULE TranMaxExists --------------------------
\*   MessageInterface -> TranFinite, Messages, Tran, and TranCard (the named
\*                       operator that lets FiniteMaxExists be applied here)
\*   TranCardNat, FiniteMaxExists -> cited lemmas
EXTENDS MessageInterface, TranCardNat, FiniteMaxExists

\* A finite, non-empty set of messages has an element of maximal Tran-size.
\* (First-order wrapper around FiniteMaxExists, so it can be applied to a set
\* given by a local definition.)
LEMMA TranMaxExists ==
    ASSUME TranFinite,
           NEW T, IsFiniteSet(T), T # {}, T \subseteq Messages
    PROVE \E r \in T : \A y \in T : Cardinality(Tran(y)) <= Cardinality(Tran(r))
<1>1. \A x \in T : TranCard(x) \in Nat
  <2>1. ASSUME NEW x \in T PROVE TranCard(x) \in Nat
    <3>1. x \in Messages  BY <2>1
    <3> QED BY <3>1, TranCardNat DEF TranCard
  <2> QED BY <2>1
<1>2. \E r \in T : \A y \in T : TranCard(y) <= TranCard(r)
  BY <1>1, FiniteMaxExists
<1> QED BY <1>2 DEF TranCard
====================================================================
