--------------------------- MODULE NatMaxExists ---------------------------
\* IdOp is one of the definitions kept in MessageInterface: FiniteMaxExists
\* cannot be applied to a locally-DEFINEd set, so it is wrapped once here for
\* an opaque NEW T that call sites can cite instead.
EXTENDS MessageInterface, FiniteMaxExists

LEMMA NatMaxExists ==
  ASSUME NEW T \in SUBSET Nat, IsFiniteSet(T), T # {}
  PROVE \E r \in T : \A y \in T : y <= r
<1>1. \A z \in T : IdOp(z) \in Nat  BY DEF IdOp
<1>2. \E r \in T : \A y \in T : IdOp(y) <= IdOp(r)  BY <1>1, FiniteMaxExists
<1> QED BY <1>2 DEF IdOp
====================================================================
