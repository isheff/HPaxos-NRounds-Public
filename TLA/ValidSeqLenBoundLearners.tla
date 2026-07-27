-------------------- MODULE ValidSeqLenBoundLearners --------------------
\* As ValidSeqLenBoundAcceptors, plus ConFromCaughtAntitone, which the proof
\* cites to turn the shrinking caught-sets into a growing connectivity chain.
EXTENDS LearnerGraphInterface, Sequences, StrictSubsetChainBound,
        ConFromCaughtAntitone

\* Any valid chain also has length bounded by Cardinality(Learners) + 1,
\* since ConFromCaught(alpha, l[i]) forms a strictly-INCREASING chain of
\* subsets of Learners (by ConFromCaughtAntitone: caught sets shrink along
\* the chain, so connectivity grows).  We reverse the derived sequence so
\* StrictSubsetChainBound (which wants a decreasing chain) applies.
LEMMA ValidSeqLenBoundLearners ==
  ASSUME FiniteLearners, NEW alpha \in Learners, NEW l \in ValidSeqs(alpha)
  PROVE Len(l) <= Cardinality(Learners) + 1
<1>1. IsFiniteSet(Learners)  BY DEF FiniteLearners
<1>2. l \in Seq(SUBSET Acceptors)  BY DEF ValidSeqs
<1>4. Len(l) \in Nat  BY <1>2
<1>5. \A i \in 1..(Len(l)-1) : l[i+1] \subseteq l[i] /\ ConFromCaught(alpha, l[i]) # ConFromCaught(alpha, l[i+1])
  BY DEF ValidSeqs
<1> DEFINE N == Len(l)
<1> DEFINE lp == [i \in 1..N |-> ConFromCaught(alpha, l[N + 1 - i])]
<1>ldom. l \in [1..N -> SUBSET Acceptors]  BY <1>2
<1>dom. lp \in [1..N -> SUBSET Learners]  BY DEF ConFromCaught
<1>chain. \A i \in 1..(N-1) : lp[i+1] \subseteq lp[i] /\ lp[i+1] # lp[i]
  <2> SUFFICES ASSUME NEW i \in 1..(N-1)
               PROVE lp[i+1] \subseteq lp[i] /\ lp[i+1] # lp[i]
    OBVIOUS
  <2>j. N - i \in 1..(N-1)  BY <1>4
  <2>1. l[(N-i)+1] \subseteq l[N-i]  BY <1>5, <2>j
  <2>2. ConFromCaught(alpha, l[N-i]) \subseteq ConFromCaught(alpha, l[(N-i)+1])
    BY <2>1, ConFromCaughtAntitone
  <2>3. ConFromCaught(alpha, l[N-i]) # ConFromCaught(alpha, l[(N-i)+1])  BY <1>5, <2>j
  <2>dom. i \in 1..N /\ i+1 \in 1..N  BY <1>4
  <2>i1. N + 1 - (i+1) = N - i  BY <1>4
  <2>4. lp[i+1] = ConFromCaught(alpha, l[N-i])  BY <2>dom, <2>i1
  <2>5. lp[i] = ConFromCaught(alpha, l[(N-i)+1])
    <3>1. N + 1 - i = (N - i) + 1  BY <1>4
    <3> QED BY <2>dom, <3>1
  <2> QED BY <2>2, <2>3, <2>4, <2>5
<1> QED BY <1>1, <1>dom, <1>4, <1>chain, StrictSubsetChainBound
====================================================================
