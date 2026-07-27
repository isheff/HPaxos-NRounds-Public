--------------------- MODULE MaxDepthFiniteAcceptors ---------------------
\* Top of the dependency graph: cites four other lemmas. Each of them already
\* EXTENDS LearnerGraphInterface, so that interface stays a single shared
\* copy rather than several INSTANCE copies.
\*   AcceptorsNonEmpty          -> Acceptors # {}
\*   LowerBoundWitness          -> <<Acceptors,{}>> is a valid chain
\*   ValidSeqLenBoundAcceptors  -> the length bound
\*   MaxDepthBound              -> assembles them into the 1..N sandwich
\* MaxDepthBound also transitively supplies Max, FS_* and Cardinality.
EXTENDS LearnerGraphInterface, Sequences,
        AcceptorsNonEmpty, LowerBoundWitness,
        ValidSeqLenBoundAcceptors, MaxDepthBound

THEOREM MaxDepthFiniteAcceptors ==
  (/\ FiniteAcceptors
   /\ LearnersNonEmpty
   /\ QuorumsNonEmpty
   /\ LearnersMightAgree
   /\ ValidLearnerGraphAssumption
   ) => \A alpha \in Learners:
  MaxDepth(alpha) \in (1..Cardinality(Acceptors))
<1> SUFFICES ASSUME FiniteAcceptors, LearnersNonEmpty, QuorumsNonEmpty,
                    LearnersMightAgree, ValidLearnerGraphAssumption,
                    NEW alpha \in Learners
             PROVE MaxDepth(alpha) \in (1..Cardinality(Acceptors))
  OBVIOUS
<1>accne. Acceptors # {}  BY AcceptorsNonEmpty
<1>lne. Learners # {}  BY DEF LearnersNonEmpty
<1>witness. <<Acceptors, {}>> \in ValidSeqs(alpha)  BY <1>accne, <1>lne, LowerBoundWitness
<1>accfin. IsFiniteSet(Acceptors)  BY DEF FiniteAcceptors
<1>cardnat. Cardinality(Acceptors) \in Nat  BY <1>accfin, FS_CardinalityType
<1>bound. \A l \in ValidSeqs(alpha) : Len(l) <= Cardinality(Acceptors) + 1
  <2> SUFFICES ASSUME NEW l \in ValidSeqs(alpha) PROVE Len(l) <= Cardinality(Acceptors) + 1  OBVIOUS
  <2> QED BY ValidSeqLenBoundAcceptors
<1> QED BY <1>bound, <1>witness, <1>cardnat, MaxDepthBound
====================================================================
