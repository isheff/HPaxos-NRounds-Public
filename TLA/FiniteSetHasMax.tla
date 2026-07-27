------------------------ MODULE FiniteSetHasMax ------------------------
\* EXTENDS, not LOCAL INSTANCE: MaxProps cites this lemma, and a lemma whose
\* STATEMENT mentions LOCAL-imported operators (here IsFiniteSet, Nat, <=)
\* cannot be cited from another module. FiniteSetTheorems EXTENDS FiniteSets,
\* Integers, Functions, WellFoundedInduction, so one line covers the statement
\* operators, the proof's FS_* theorems, and GeneralNatInduction -- and keeps
\* a single shared copy of FiniteSets rather than an EXTENDS/INSTANCE pair.
EXTENDS FiniteSetTheorems

\* Declares no set/arithmetic operators, so it cannot collide; proof-only.
LOCAL INSTANCE TLAPS                \* IsaM

\* Generic existence of a maximum for a finite, non-empty set of naturals.
LEMMA FiniteSetHasMax ==
  ASSUME NEW D, IsFiniteSet(D), D # {}, \A x \in D : x \in Nat
  PROVE \E r \in D : \A y \in D : y <= r
<1> DEFINE Q(n) == \A U : (IsFiniteSet(U) /\ Cardinality(U) = n /\ U # {}
                            /\ (\A z \in U : z \in Nat))
                          => (\E r \in U : \A y \in U : y <= r)
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. Cardinality(D) \in Nat  BY FS_CardinalityType
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW U, IsFiniteSet(U), Cardinality(U) = n, U # {},
                      \A z \in U : z \in Nat
               PROVE  \E r \in U : \A y \in U : y <= r
    OBVIOUS
  <2>x. PICK x \in U : TRUE  OBVIOUS
  <2>pos. Cardinality(U) >= 1  BY FS_EmptySet, FS_CardinalityType
  <2>n1. n - 1 \in Nat  BY <2>pos
  <2>U2. IsFiniteSet(U \ {x}) /\ Cardinality(U \ {x}) = n - 1
    BY <2>x, FS_RemoveElement
  <2>1. CASE U \ {x} = {}
    <3>1. \A y \in U : y <= x
      <4>1. ASSUME NEW y \in U PROVE y <= x
        <5>1. y = x  BY <2>1, <4>1
        <5> QED BY <5>1
      <4> QED BY <4>1
    <3> QED BY <3>1, <2>x
  <2>2. CASE U \ {x} # {}
    <3>k. n - 1 \in 0..(n-1)  BY <2>n1
    <3>ih. \E r \in (U \ {x}) : \A y \in (U \ {x}) : y <= r
      BY <3>k, <2>U2, <2>2
    <3> PICK r \in (U \ {x}) : \A y \in (U \ {x}) : y <= r  BY <3>ih
    <3>rnat. r \in Nat  OBVIOUS
    <3>xnat. x \in Nat  BY <2>x
    <3>1. CASE x <= r
      <4> QED BY <3>1
    <3>2. CASE x > r
      <4> QED BY <3>2, <3>rnat, <3>xnat
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
