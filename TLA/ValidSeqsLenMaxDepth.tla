----------------------- MODULE ValidSeqsLenMaxDepth -----------------------
\*   FiniteSetTheorems         -> FS_CardinalityType, FS_Interval, FS_Subset
\*   ValidSeqLenBoundAcceptors, MaxProps -> cited lemmas (from the
\*                                LearnerGraphInterface split)
EXTENDS MessageInterface, FiniteSetTheorems,
        ValidSeqLenBoundAcceptors, MaxProps

\* MaxDepth is the maximum over ValidSeqs lengths (minus one): no valid
\* chain exceeds it.
LEMMA ValidSeqsLenMaxDepth ==
  ASSUME FiniteAcceptors, LearnersNonEmpty, QuorumsNonEmpty,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW l \in ValidSeqs(alpha)
  PROVE Len(l) - 1 <= MaxDepth(alpha)
<1> DEFINE D == {Len(s)-1 : s \in ValidSeqs(alpha)}
<1> DEFINE L == {Len(s) : s \in ValidSeqs(alpha)}
<1>accfin. IsFiniteSet(Acceptors)  BY DEF FiniteAcceptors
<1>Nnat. Cardinality(Acceptors) \in Nat  BY <1>accfin, FS_CardinalityType
<1>bound. \A s \in ValidSeqs(alpha) : Len(s) <= Cardinality(Acceptors) + 1
  <2> SUFFICES ASSUME NEW s \in ValidSeqs(alpha) PROVE Len(s) <= Cardinality(Acceptors) + 1  OBVIOUS
  <2> QED BY ValidSeqLenBoundAcceptors
<1>Lsub. L \subseteq 0..(Cardinality(Acceptors)+1)
  <2> SUFFICES ASSUME NEW k \in L PROVE k \in 0..(Cardinality(Acceptors)+1)  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : k = Len(s)  OBVIOUS
  <2>2. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2>3. Len(s) <= Cardinality(Acceptors) + 1  BY <2>1, <1>bound
  <2> QED BY <2>1, <2>2, <2>3
<1>rangefin. IsFiniteSet(0..(Cardinality(Acceptors)+1))  BY <1>Nnat, FS_Interval
<1>Lfin. IsFiniteSet(L)  BY <1>Lsub, <1>rangefin, FS_Subset
<1>lIn. Len(l) \in L  OBVIOUS
<1>Lne. L # {}  BY <1>lIn
<1>Lnat. \A x \in L : x \in Nat  BY <1>Lsub
<1>maxprops. Max(L) \in L /\ (\A y \in L : Max(L) >= y)  BY <1>Lfin, <1>Lne, <1>Lnat, MaxProps
<1>MaxLnat. Max(L) \in Nat  BY <1>maxprops, <1>Lsub
<1>d_witness. Max(L) - 1 \in D  BY <1>maxprops
<1>d_upper. \A d \in D : d <= Max(L) - 1
  <2> SUFFICES ASSUME NEW d \in D PROVE d <= Max(L) - 1  OBVIOUS
  <2>1. PICK s \in ValidSeqs(alpha) : d = Len(s) - 1  OBVIOUS
  <2>2. Len(s) \in L  BY <2>1
  <2>3. Len(s) <= Max(L)  BY <2>2, <1>maxprops
  <2>4. Len(s) \in Nat  BY <2>1 DEF ValidSeqs
  <2> QED BY <2>1, <2>3, <2>4, <1>MaxLnat
<1>witness2. \E x \in D : \A y \in D : x >= y
  BY <1>d_witness, <1>d_upper
<1>maxprops2. MaxDepth(alpha) \in D /\ (\A y \in D : MaxDepth(alpha) >= y)
  BY <1>witness2 DEF MaxDepth, Max
<1>lIn2. Len(l) - 1 \in D  OBVIOUS
<1> QED BY <1>maxprops2, <1>lIn2
====================================================================
