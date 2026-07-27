----------------------------- MODULE CQFinite -----------------------------
EXTENDS MessageInterface, FiniteSetTheorems

LEMMA CQFinite ==
  ASSUME LearnerGraphAssumptions, NEW mm \in SUBSET Messages
  PROVE IsFiniteSet(CQ(mm))
<1>acc. IsFiniteSet(Acceptors)  BY DEF LearnerGraphAssumptions, FiniteAcceptors
<1>lrn. IsFiniteSet(Learners)  BY DEF LearnerGraphAssumptions, FiniteLearners
<1>caughtsub. CaughtAcc(mm) \subseteq Acceptors  BY DEF CaughtAcc, CaughtS
<1>caughtfin. IsFiniteSet(CaughtAcc(mm))  BY <1>acc, <1>caughtsub, FS_Subset
<1>relsub. RelevantLearners(mm) \subseteq Learners  BY DEF RelevantLearners
<1>relfin. IsFiniteSet(RelevantLearners(mm))  BY <1>lrn, <1>relsub, FS_Subset
<1>p1. IsFiniteSet({CatchWitness1(mm,s) : s \in CaughtAcc(mm)})  BY <1>caughtfin, FS_Image
<1>p2. IsFiniteSet({CatchWitness2(mm,s) : s \in CaughtAcc(mm)})  BY <1>caughtfin, FS_Image
<1>p3. IsFiniteSet({TopLearnerMsg(mm,beta) : beta \in RelevantLearners(mm)})  BY <1>relfin, FS_Image
<1>u12. IsFiniteSet({CatchWitness1(mm,s) : s \in CaughtAcc(mm)}
                    \cup {CatchWitness2(mm,s) : s \in CaughtAcc(mm)})
  BY <1>p1, <1>p2, FS_Union
<1> QED BY <1>u12, <1>p3, FS_Union DEF CQ
====================================================================
