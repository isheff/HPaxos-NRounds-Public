------------------------- MODULE FiniteMaxExists -------------------------
\* Purely generic: the statement mentions no MessageInterface definition at
\* all, so this module does NOT extend it.
\*   FiniteSetTheorems -> IsFiniteSet, Cardinality, Nat (statement) plus
\*                        FS_CardinalityType / FS_EmptySet / FS_RemoveElement
\*                        and GeneralNatInduction (via WellFoundedInduction)
\*   TLAPS             -> IsaM, proof-only; declares no set/arithmetic
\*                        operator, so it cannot collide and may stay LOCAL.
EXTENDS FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* A finite non-empty set has an element maximizing any Nat-valued function.
LEMMA FiniteMaxExists ==
    ASSUME NEW S, IsFiniteSet(S), S # {}, NEW f(_),
           \A x \in S : f(x) \in Nat
    PROVE \E r \in S : \A y \in S : f(y) <= f(r)
<1> DEFINE Q(n) == \A U : (IsFiniteSet(U) /\ Cardinality(U) = n /\ U # {}
                            /\ (\A z \in U : f(z) \in Nat))
                          => (\E r \in U : \A y \in U : f(y) <= f(r))
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. Cardinality(S) \in Nat  BY FS_CardinalityType
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW U, IsFiniteSet(U), Cardinality(U) = n, U # {},
                      \A z \in U : f(z) \in Nat
               PROVE  \E r \in U : \A y \in U : f(y) <= f(r)
    OBVIOUS
  <2>x. PICK x \in U : TRUE  OBVIOUS
  <2>fx. f(x) \in Nat  BY <2>x
  <2>pos. Cardinality(U) >= 1  BY FS_EmptySet, FS_CardinalityType
  <2>n1. n - 1 \in Nat  BY <2>pos
  <2>U2. IsFiniteSet(U \ {x}) /\ Cardinality(U \ {x}) = n - 1
    BY <2>x, FS_RemoveElement
  <2>1. CASE U \ {x} = {}
    <3>1. \A y \in U : f(y) <= f(x)
      <4>1. ASSUME NEW y \in U PROVE f(y) <= f(x)
        <5>1. y = x  BY <2>1, <4>1
        <5> QED BY <5>1, <2>fx
      <4> QED BY <4>1
    <3> QED BY <3>1, <2>x
  <2>2. CASE U \ {x} # {}
    <3>k. n - 1 \in 0..(n-1)  BY <2>n1
    <3>z. \A z \in U \ {x} : f(z) \in Nat  OBVIOUS
    <3>IH. \E r \in U \ {x} : \A y \in U \ {x} : f(y) <= f(r)
      <4>1. Q(n-1)  BY <3>k
      <4> QED BY <4>1, <2>U2, <2>2, <3>z
    <3>r. PICK r \in U \ {x} : \A y \in U \ {x} : f(y) <= f(r)  BY <3>IH
    <3>rU. r \in U  BY <3>r
    <3>fr. f(r) \in Nat  BY <3>rU
    <3>1. CASE f(x) <= f(r)
      <4>1. \A y \in U : f(y) <= f(r)
        <5>1. ASSUME NEW y \in U PROVE f(y) <= f(r)
          <6>1. CASE y = x  BY <6>1, <3>1
          <6>2. CASE y # x  BY <6>2, <3>r
          <6> QED BY <6>1, <6>2
        <5> QED BY <5>1
      <4> QED BY <4>1, <3>rU
    <3>2. CASE ~(f(x) <= f(r))
      <4>1. \A y \in U : f(y) <= f(x)
        <5>1. ASSUME NEW y \in U PROVE f(y) <= f(x)
          <6>1. CASE y = x  BY <6>1, <2>fx
          <6>2. CASE y # x
            <7>1. y \in U \ {x}  BY <6>2
            <7>2. f(y) <= f(r) /\ f(y) \in Nat  BY <7>1, <3>r
            <7> QED BY <7>2, <3>fr, <2>fx, <3>2
          <6> QED BY <6>1, <6>2
        <5> QED BY <5>1
      <4> QED BY <4>1, <2>x
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
