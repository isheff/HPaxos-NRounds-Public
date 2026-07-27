--------------------- MODULE MaxDepthFiniteLearners ---------------------
\* Mirror of MaxDepthFiniteAcceptors, bounding by Cardinality(Learners)
\* instead, so it cites ValidSeqLenBoundLearners rather than
\* ValidSeqLenBoundAcceptors.
EXTENDS LearnerGraphInterface, Sequences,
        AcceptorsNonEmpty, LowerBoundWitness,
        ValidSeqLenBoundLearners, MaxDepthBound

THEOREM MaxDepthFiniteLearners ==
  (/\ FiniteLearners
   /\ LearnersNonEmpty
   /\ QuorumsNonEmpty
   /\ LearnersMightAgree
   /\ ValidLearnerGraphAssumption
   ) => \A alpha \in Learners:
  MaxDepth(alpha) \in (1..Cardinality(Learners))
<1> SUFFICES ASSUME FiniteLearners, LearnersNonEmpty, QuorumsNonEmpty,
                    LearnersMightAgree, ValidLearnerGraphAssumption,
                    NEW alpha \in Learners
             PROVE MaxDepth(alpha) \in (1..Cardinality(Learners))
  OBVIOUS
<1>lnefin. IsFiniteSet(Learners)  BY DEF FiniteLearners
<1>lne. Learners # {}  BY DEF LearnersNonEmpty
<1>accne. Acceptors # {}  BY AcceptorsNonEmpty
<1>witness. <<Acceptors, {}>> \in ValidSeqs(alpha)  BY <1>accne, <1>lne, LowerBoundWitness
<1>cardnat. Cardinality(Learners) \in Nat  BY <1>lnefin, FS_CardinalityType
<1>bound. \A l \in ValidSeqs(alpha) : Len(l) <= Cardinality(Learners) + 1
  <2> SUFFICES ASSUME NEW l \in ValidSeqs(alpha) PROVE Len(l) <= Cardinality(Learners) + 1  OBVIOUS
  <2> QED BY ValidSeqLenBoundLearners
<1> QED BY <1>bound, <1>witness, <1>cardnat, MaxDepthBound
====================================================================
