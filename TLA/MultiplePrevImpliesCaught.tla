------------------- MODULE MultiplePrevImpliesCaught -------------------
\*   FiniteSetTheorems -> FS_Subset, FS_CardinalityType, FS_EmptySet,
\*                        FS_RemoveElement
\*   TLAPS             -> SMT; proof-only
EXTENDS MessageInterface, FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* If m has more than one Prev, two distinct maximal same-signer ancestors of m
\* are pairwise incomparable, which is exactly what it means for Sig(m) to be
\* Caught.
THEOREM MultiplePrevImpliesCaught ==
  ASSUME TranFinite, NEW m \in Messages,
         Sig(m) \in Acceptors, Cardinality(Prev(m)) > 1
  PROVE Sig(m) \in Caught(m)
<1>subT. Prev(m) \subseteq Tran(m)  BY DEF Prev, TranExclusive
<1>finT. IsFiniteSet(Tran(m))  BY DEF TranFinite
<1>fin. IsFiniteSet(Prev(m))  BY <1>subT, <1>finT, FS_Subset
<1>cardNat. Cardinality(Prev(m)) \in Nat  BY <1>fin, FS_CardinalityType
<1>ne. Prev(m) # {}  BY FS_EmptySet
<1>x1. PICK x1 \in Prev(m) : TRUE  BY <1>ne
<1>rem. IsFiniteSet(Prev(m) \ {x1}) /\ Cardinality(Prev(m) \ {x1}) = Cardinality(Prev(m)) - 1
  BY <1>fin, <1>x1, FS_RemoveElement
<1>ne2. Prev(m) \ {x1} # {}
  <2>1. Cardinality(Prev(m) \ {x1}) > 0  BY <1>rem, <1>cardNat, SMT
  <2> QED BY <2>1, FS_EmptySet
<1>x2. PICK x2 \in Prev(m) \ {x1} : TRUE  BY <1>ne2
<1>x2In. x2 \in Prev(m) /\ x2 # x1  BY <1>x2
<1>1. x1 \in TranExclusive(m) /\ Sig(x1) = Sig(m)
      /\ \A y \in TranExclusive(m): x1 \in TranExclusive(y) => Sig(x1) # Sig(y)  BY <1>x1 DEF Prev
<1>2. x2 \in TranExclusive(m) /\ Sig(x2) = Sig(m)
      /\ \A y \in TranExclusive(m): x2 \in TranExclusive(y) => Sig(x2) # Sig(y)  BY <1>x2In DEF Prev
<1>3. x1 \in Tran(m) /\ x2 \in Tran(m)  BY <1>1, <1>2 DEF TranExclusive
<1>4. x1 \notin Tran(x2)  BY <1>1, <1>2, <1>x2In DEF TranExclusive
<1>5. x2 \notin Tran(x1)  BY <1>1, <1>2, <1>x2In DEF TranExclusive
<1>6. \E m1 \in Tran(m): \E m2 \in Tran(m):
        Sig(m1) = Sig(m) /\ Sig(m2) = Sig(m) /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
  BY <1>1, <1>2, <1>3, <1>4, <1>5
<1> QED BY <1>6 DEF Caught, CaughtS
====================================================================
