--------------------- MODULE StrictSubsetChainBound ---------------------
\* EXTENDS, not LOCAL INSTANCE. Two reasons, both load-bearing:
\*  (1) A lemma whose STATEMENT mentions LOCAL-imported operators cannot be
\*      cited from another module -- the citation fails to instantiate.
\*      ValidSeqLenBoundAcceptors/Learners cite this lemma.
\*  (2) EXTENDS SHARES a module; INSTANCE COPIES it. Mixing the two for the
\*      same base (e.g. EXTENDS FiniteSets + LOCAL INSTANCE FiniteSetTheorems)
\*      puts two distinct copies of IsFiniteSet in scope, which SANY renames
\*      apart to IsFiniteSet_1 -- and then nothing matches.
\* FiniteSetTheorems EXTENDS FiniteSets, Integers, Functions,
\* WellFoundedInduction, so this single line supplies the statement operators
\* (IsFiniteSet, Cardinality, Nat, arithmetic) AND the proof's FS_* theorems
\* AND GeneralNatInduction.
EXTENDS FiniteSetTheorems

\* TLAPS declares no set/arithmetic operators, so it cannot collide; it is
\* needed only inside the proof, for IsaM.
LOCAL INSTANCE TLAPS

\* A chain of length N of strictly-decreasing subsets of a finite set X has
\* N <= Cardinality(X) + 1 (a maximal chain runs from a set of size
\* Cardinality(X) down to the empty set).
LEMMA StrictSubsetChainBound ==
  ASSUME NEW X, IsFiniteSet(X), NEW N \in Nat, NEW l \in [1..N -> SUBSET X],
         \A i \in 1..(N-1) : l[i+1] \subseteq l[i] /\ l[i+1] # l[i]
  PROVE N <= Cardinality(X) + 1
<1>Xnat. Cardinality(X) \in Nat  BY FS_CardinalityType
<1> DEFINE Q(i) == i \in 1..N => Cardinality(l[i]) + i <= Cardinality(X) + 1
<1>allQ. \A i \in Nat : Q(i)
  <2> HIDE DEF Q
  <2>ind. \A i \in Nat : (\A k \in 0..(i-1) : Q(k)) => Q(i)
    <3> USE DEF Q
    <3> SUFFICES ASSUME NEW i \in Nat, \A k \in 0..(i-1) : Q(k), i \in 1..N
                 PROVE Cardinality(l[i]) + i <= Cardinality(X) + 1
      OBVIOUS
    <3>1. CASE i = 1
      <4>1. l[i] \in SUBSET X  OBVIOUS
      <4>2. Cardinality(l[i]) <= Cardinality(X)  BY <4>1, FS_Subset
      <4>3. Cardinality(l[i]) \in Nat  BY <4>1, FS_Subset, FS_CardinalityType
      <4> QED BY <3>1, <4>2, <4>3, <1>Xnat
    <3>2. CASE i > 1
      <4>im1. i - 1 \in 1..N  BY <3>2
      <4>ihk. i - 1 \in 0..(i-1)  OBVIOUS
      <4>ih. Q(i-1)  BY <4>ihk
      <4>ihE. Cardinality(l[i-1]) + (i-1) <= Cardinality(X) + 1  BY <4>ih, <4>im1
      <4>j. i - 1 \in 1..(N-1)  BY <3>2
      <4>sub. l[i] \subseteq l[i-1] /\ l[i] # l[i-1]  BY <4>j
      <4>l1fin. l[i-1] \in SUBSET X  BY <4>im1
      <4>l1finset. IsFiniteSet(l[i-1])  BY <4>l1fin, FS_Subset
      <4>card. Cardinality(l[i]) < Cardinality(l[i-1])  BY <4>sub, <4>l1finset, FS_Subset
      <4>types. Cardinality(l[i]) \in Nat /\ Cardinality(l[i-1]) \in Nat
        BY <4>l1finset, FS_CardinalityType, <4>sub, FS_Subset
      <4>itypes. i \in Nat /\ i >= 2  BY <3>2
      <4>im1val. i - 1 + 1 = i  BY <4>itypes
      <4> QED BY <4>ihE, <4>card, <4>types, <4>itypes, <1>Xnat, <4>im1val
    <3> QED BY <3>1, <3>2
  <2> QED BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>caseZero. CASE N = 0
  <2> QED BY <1>caseZero, <1>Xnat
<1>casePos. CASE N > 0
  <2>N. N \in 1..N  BY <1>casePos
  <2>QN. Cardinality(l[N]) + N <= Cardinality(X) + 1  BY <1>allQ, <2>N
  <2>lNfin. l[N] \in SUBSET X  BY <2>N
  <2>lNfinset. IsFiniteSet(l[N])  BY <2>lNfin, FS_Subset
  <2>card0. Cardinality(l[N]) \in Nat  BY <2>lNfinset, FS_CardinalityType
  <2>Nnat. N \in Nat  OBVIOUS
  <2> QED BY <2>QN, <2>card0, <2>Nnat, <1>Xnat, <1>casePos
<1> QED BY <1>caseZero, <1>casePos
====================================================================
