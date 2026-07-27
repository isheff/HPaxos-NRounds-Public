-------------------------- MODULE CFiniteSubsetBounded --------------------------
EXTENDS MessageConcrete, CMinLevelDom, CMCALMonoGen, FiniteSetTheorems,
        NaturalsInduction
LOCAL INSTANCE TLAPS

LEMMA CFiniteSubsetBounded ==
  ASSUME NEW S, IsFiniteSet(S), S \subseteq CMC
  PROVE \E L \in Nat : \A z \in S : z \in CMCAL[L]
<1> DEFINE Q(n) == \A T : (IsFiniteSet(T) /\ Cardinality(T) = n /\ T \subseteq CMC)
                          => (\E L \in Nat : \A z \in T : z \in CMCAL[L])
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. Cardinality(S) \in Nat  BY FS_CardinalityType
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW T, IsFiniteSet(T), Cardinality(T) = n, T \subseteq CMC
               PROVE  \E L \in Nat : \A z \in T : z \in CMCAL[L]
    OBVIOUS
  <2>1. CASE T = {}
    <3> QED BY <2>1
  <2>2. CASE T # {}
    <3>x. PICK x \in T : TRUE  BY <2>2
    <3>pos. Cardinality(T) >= 1  BY FS_EmptySet, FS_CardinalityType
    <3>n1. n - 1 \in Nat  BY <3>pos
    <3>T2. IsFiniteSet(T \ {x}) /\ Cardinality(T \ {x}) = n - 1
      BY <3>x, FS_RemoveElement
    <3>T2sub. (T \ {x}) \subseteq CMC  BY <2>2
    <3>k. n - 1 \in 0..(n-1)  BY <3>n1
    <3>ih. \E L \in Nat : \A z \in (T \ {x}) : z \in CMCAL[L]
      BY <3>k, <3>T2, <3>T2sub
    <3> PICK L1 \in Nat : \A z \in (T \ {x}) : z \in CMCAL[L1]  BY <3>ih
    <3>picked. \A z \in (T \ {x}) : z \in CMCAL[L1]  OBVIOUS
    <3>xmc. x \in CMC  BY <3>x, <2>2
    <3>L2. CMinLevel(x) \in Nat /\ x \in CMCAL[CMinLevel(x)]  BY <3>xmc, CMinLevelDom
    <3> DEFINE Lmax == IF L1 >= CMinLevel(x) THEN L1 ELSE CMinLevel(x)
    <3>Lmaxnat. Lmax \in Nat  BY <3>L2
    <3>1. \A z \in (T \ {x}) : z \in CMCAL[Lmax]
      <4> SUFFICES ASSUME NEW z \in (T \ {x}) PROVE z \in CMCAL[Lmax]  OBVIOUS
      <4>1. z \in CMCAL[L1]  BY <3>picked
      <4> QED BY <4>1, <3>Lmaxnat, CMCALMonoGen
    <3>2. x \in CMCAL[Lmax]  BY <3>L2, <3>Lmaxnat, CMCALMonoGen
    <3>3. \A z \in T : z \in CMCAL[Lmax]
      <4> SUFFICES ASSUME NEW z \in T PROVE z \in CMCAL[Lmax]  OBVIOUS
      <4>1. CASE z = x  BY <4>1, <3>2
      <4>2. CASE z # x
        <5>1. z \in (T \ {x})  BY <4>2
        <5> QED BY <5>1, <3>1
      <4> QED BY <4>1, <4>2
    <3> QED BY <3>3, <3>Lmaxnat
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
=============================================================================
