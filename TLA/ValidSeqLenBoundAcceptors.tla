-------------------- MODULE ValidSeqLenBoundAcceptors --------------------
\* Statement mentions FiniteAcceptors / Learners / ValidSeqs / Acceptors
\* (LearnerGraphInterface), Len (Sequences), and Cardinality (reached via
\* StrictSubsetChainBound -> FiniteSetTheorems -> FiniteSets).
\* All EXTENDS: MaxDepthFiniteAcceptors cites this lemma, and a lemma whose
\* statement mentions LOCAL-imported operators cannot be cited elsewhere.
EXTENDS LearnerGraphInterface, Sequences, StrictSubsetChainBound

\* Any valid chain has length bounded by Cardinality(Acceptors) + 1, since
\* the l[i] themselves form a strictly-decreasing chain of subsets of
\* Acceptors.
LEMMA ValidSeqLenBoundAcceptors ==
  ASSUME FiniteAcceptors, NEW alpha \in Learners, NEW l \in ValidSeqs(alpha)
  PROVE Len(l) <= Cardinality(Acceptors) + 1
<1>1. IsFiniteSet(Acceptors)  BY DEF FiniteAcceptors
<1>2. l \in Seq(SUBSET Acceptors)  BY DEF ValidSeqs
<1>3. l \in [1..Len(l) -> SUBSET Acceptors]  BY <1>2
<1>4. Len(l) \in Nat  BY <1>2
<1>5. \A i \in 1..(Len(l)-1) : l[i+1] \subseteq l[i] /\ l[i+1] # l[i]  BY DEF ValidSeqs
<1> QED BY <1>1, <1>3, <1>4, <1>5, StrictSubsetChainBound
====================================================================
