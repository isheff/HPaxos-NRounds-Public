--------------- MODULE LearnerGraphConcreteSupportsAssumptions ---------------
EXTENDS LearnerGraphConcrete, Fields, FiniteSetTheorems,
        ValidReduction, ConcreteValid, CondensedReduction, ConcreteCondensed,
        ConcreteSafetyType, ConcreteQuorumType,
        ConcreteFiniteAcceptors, ConcreteFiniteLearners,
        ConcreteLearnersNonEmpty, ConcreteQuorumsNonEmpty, ConcreteLearnersMightAgree

THEOREM LearnerGraphConcreteSupportsAssumptions ==
  LearnerGraphInterface = CLGI => LearnerGraphAssumptions
  <1> SUFFICES ASSUME LearnerGraphInterface = CLGI PROVE LearnerGraphAssumptions OBVIOUS
  <1>1. SafetySetsTypeOK BY ConcreteSafetyType
  <1>2. QuorumsTypeOK BY ConcreteQuorumType
  <1>3. ValidLearnerGraphAssumption BY ValidReduction, ConcreteValid
  <1>4. Acceptors = CAcc BY Fields
  <1>5. IsFiniteSet(Acceptors) BY <1>4, FS_Interval DEF CAcc
  <1>6. CondensedLearnerGraphAssumption BY <1>5, CondensedReduction, ConcreteCondensed
  <1>7. FiniteAcceptors BY ConcreteFiniteAcceptors
  <1>8. FiniteLearners BY ConcreteFiniteLearners
  <1>9. LearnersNonEmpty BY ConcreteLearnersNonEmpty
  <1>10. QuorumsNonEmpty BY ConcreteQuorumsNonEmpty
  <1>11. LearnersMightAgree BY ConcreteLearnersMightAgree
  <1> QED BY <1>1, <1>2, <1>3, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11 DEF LearnerGraphAssumptions
=============================================================================
