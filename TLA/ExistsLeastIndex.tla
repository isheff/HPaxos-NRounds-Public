------------------------- MODULE ExistsLeastIndex -------------------------
\* Purely generic (naturals only): no MessageInterface definition appears in
\* the statement, so this module does not extend it.
\*   FiniteSetTheorems -> Nat and GeneralNatInduction
\*   TLAPS             -> IsaM; proof-only
EXTENDS FiniteSetTheorems
LOCAL INSTANCE TLAPS

\* Any nonempty set of naturals has a least element -- used to pick the
\* EARLIEST chain index at which a learner is connected.
LEMMA ExistsLeastIndex ==
  ASSUME NEW S \in SUBSET Nat, S # {}
  PROVE \E i \in S : \A j \in S : i <= j
<1> DEFINE Q(n) == \A T \in SUBSET Nat : n \in T => \E i \in T : \A j \in T : i <= j
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. PICK s0 \in S : TRUE  OBVIOUS
  <2>2. s0 \in Nat  OBVIOUS
  <2> QED BY <2>1, <2>2 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                      NEW T \in SUBSET Nat, n \in T
               PROVE \E i \in T : \A j \in T : i <= j
    OBVIOUS
  <2> DEFINE T2 == {j \in T : j < n}
  <2>1. CASE T2 = {}
    <3>1. \A j \in T : n <= j
      <4> SUFFICES ASSUME NEW j \in T PROVE n <= j  OBVIOUS
      <4>1. j \in Nat  OBVIOUS
      <4> QED BY <2>1, <4>1
    <3> QED BY <3>1
  <2>2. CASE T2 # {}
    <3>1. PICK t2 \in T2 : TRUE  BY <2>2
    <3>2. t2 \in T /\ t2 < n /\ t2 \in Nat  BY <3>1
    <3>3. t2 \in 0..(n-1)  BY <3>2
    <3>4. Q(t2)  BY <3>3
    <3> QED BY <3>4, <3>2
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
