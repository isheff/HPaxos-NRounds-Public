---------------------------- MODULE CMaxLevelElement ----------------------------
EXTENDS MessageConcrete, CMinLevelDom, FiniteSetTheorems, NaturalsInduction
LOCAL INSTANCE TLAPS

LEMMA CMaxLevelElement ==
  ASSUME NEW S, IsFiniteSet(S), S # {}, S \subseteq CMC
  PROVE \E x \in S : \A y \in S : CMinLevel(y) <= CMinLevel(x)
<1> DEFINE lev(z) == CMinLevel(z)
<1> DEFINE P(n) == \A T : (IsFiniteSet(T) /\ T # {} /\ Cardinality(T) = n /\ T \subseteq CMC)
                          => \E x \in T : \A y \in T : lev(y) <= lev(x)
<1>card. Cardinality(S) \in Nat  BY FS_CardinalityType
<1> SUFFICES \A n \in Nat : P(n)  BY <1>card
<1> HIDE DEF P
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : P(kk)) => P(n)
  <2> USE DEF P
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : P(kk),
                      NEW T, IsFiniteSet(T), T # {}, Cardinality(T) = n, T \subseteq CMC
               PROVE  \E x \in T : \A y \in T : lev(y) <= lev(x)
    OBVIOUS
  <2>1. n # 0  BY FS_EmptySet
  <2>2. PICK x0 \in T : TRUE  OBVIOUS
  <2> DEFINE T0 == T \ {x0}
  <2>3. IsFiniteSet(T0) /\ T0 \subseteq CMC  BY FS_Subset
  <2>4. Cardinality(T0) = n - 1
    <3>1. T = T0 \cup {x0}  BY <2>2
    <3>2. x0 \notin T0  OBVIOUS
    <3>3. Cardinality(T) = Cardinality(T0) + 1  BY <2>3, <3>1, <3>2, FS_AddElement
    <3>4. Cardinality(T0) \in Nat  BY <2>3, FS_CardinalityType
    <3> QED BY <3>3, <3>4
  <2>5. CASE T0 = {}
    <3>1. T = {x0}  BY <2>2, <2>5
    <3>x0mc. x0 \in CMC  BY <2>2
    <3>x0lev. lev(x0) \in Nat  BY <3>x0mc, CMinLevelDom
    <3>2. \A y \in T : lev(y) <= lev(x0)
      <4> SUFFICES ASSUME NEW y \in T PROVE lev(y) <= lev(x0)  OBVIOUS
      <4>1. y = x0  BY <3>1
      <4>2. lev(x0) <= lev(x0)  BY <3>x0lev
      <4> QED BY <4>1, <4>2
    <3>3. x0 \in T /\ (\A y \in T : lev(y) <= lev(x0))  BY <2>2, <3>2
    <3> QED BY <3>3
  <2>6. CASE T0 # {}
    <3>k. n - 1 \in 0..(n-1)  BY <2>4, FS_CardinalityType, <2>3
    <3>ih. \E x \in T0 : \A y \in T0 : lev(y) <= lev(x)  BY <3>k, <2>3, <2>6, <2>4
    <3> PICK x1 \in T0 : \A y \in T0 : lev(y) <= lev(x1)  BY <3>ih
    <3>x1max. \A y \in T0 : lev(y) <= lev(x1)  OBVIOUS
    <3>x0mc. x0 \in CMC  BY <2>2
    <3>x1mc. x1 \in CMC  BY <2>3
    <3>l0. lev(x0) \in Nat  BY <3>x0mc, CMinLevelDom
    <3>l1. lev(x1) \in Nat  BY <3>x1mc, CMinLevelDom
    <3>1. CASE lev(x0) >= lev(x1)
      <4>a. \A y \in T : lev(y) <= lev(x0)
        <5> SUFFICES ASSUME NEW y \in T PROVE lev(y) <= lev(x0)  OBVIOUS
        <5>1. CASE y = x0  BY <5>1, <3>l0
        <5>2. CASE y # x0
          <6>1. y \in T0  BY <5>2, <2>2
          <6>2. lev(y) <= lev(x1)  BY <6>1, <3>x1max
          <6>3. lev(y) \in Nat  BY <6>1, <2>3, CMinLevelDom
          <6> QED BY <6>2, <6>3, <3>1, <3>l0, <3>l1, SMT
        <5> QED BY <5>1, <5>2
      <4>witness. x0 \in T /\ (\A y \in T : lev(y) <= lev(x0))  BY <2>2, <4>a
      <4> QED BY <4>witness
    <3>2. CASE lev(x0) < lev(x1)
      <4>a. \A y \in T : lev(y) <= lev(x1)
        <5> SUFFICES ASSUME NEW y \in T PROVE lev(y) <= lev(x1)  OBVIOUS
        <5>1. CASE y = x0  BY <5>1, <3>2, <3>l0, <3>l1
        <5>2. CASE y # x0
          <6>1. y \in T0  BY <5>2, <2>2
          <6> QED BY <6>1, <3>x1max
        <5> QED BY <5>1, <5>2
      <4>x1T. x1 \in T  BY <2>2
      <4>witness. x1 \in T /\ (\A y \in T : lev(y) <= lev(x1))  BY <4>x1T, <4>a
      <4> QED BY <4>witness
    <3> QED BY <3>1, <3>2, <3>l0, <3>l1
  <2> QED BY <2>5, <2>6
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
=============================================================================
