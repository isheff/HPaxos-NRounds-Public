----------------------------- MODULE CMinLevelDom -----------------------------
\* NaturalsInduction supplies SmallestNatural. Min is unfolded (DEF Min) at
\* <1>4, so it must be the shared FiniteSetsExt copy reached through
\* MessageConcrete -> MessageInterface -> LearnerGraphInterface, not a private one.
EXTENDS MessageConcrete, NaturalsInduction

LEMMA CMinLevelDom ==
  ASSUME NEW z \in CMC
  PROVE /\ CMinLevel(z) \in Nat
        /\ z \in CMCAL[CMinLevel(z)]
        /\ \A k \in Nat : z \in CMCAL[k] => CMinLevel(z) <= k
<1> DEFINE LS == {l \in Nat : z \in CMCAL[l]}
<1> DEFINE P(k) == z \in CMCAL[k]
<1>a. PICK n \in Nat : P(n)  BY DEF CMC
<1>2. \E m \in Nat : P(m) /\ \A k \in 0..m-1 : ~P(k)
  <2> HIDE DEF P
  <2> QED BY <1>a, SmallestNatural
<1>3. \E x \in LS : \A y \in LS : x =< y
  <2>1. PICK m \in Nat : P(m) /\ \A k \in 0..m-1 : ~P(k)  BY <1>2
  <2>2. m \in LS  BY <2>1
  <2>3. \A y \in LS : m =< y
    <3>1. ASSUME NEW y \in LS PROVE m =< y  BY <2>1, <3>1
    <3> QED BY <3>1
  <2> QED BY <2>2, <2>3
<1>4. CMinLevel(z) \in LS /\ (\A y \in LS : CMinLevel(z) =< y)
  BY <1>3 DEF CMinLevel, Min
<1> QED
  <2>1. CMinLevel(z) \in Nat /\ z \in CMCAL[CMinLevel(z)]  BY <1>4
  <2>2. \A k \in Nat : z \in CMCAL[k] => CMinLevel(z) <= k
    <3>1. ASSUME NEW k \in Nat, z \in CMCAL[k] PROVE CMinLevel(z) <= k
      <4>1. k \in LS  BY <3>1
      <4> QED BY <1>4, <4>1
    <3> QED BY <3>1
  <2> QED BY <2>1, <2>2
=============================================================================
