------------------------ MODULE ConcreteFiniteLearners ------------------------
EXTENDS LearnerGraphConcrete, Fields, FiniteSetTheorems

LEMMA ConcreteFiniteLearners == ASSUME LearnerGraphInterface = CLGI PROVE FiniteLearners
  <1>1. Learners = CLrn BY Fields
  <1>2. IsFiniteSet(CLrn) BY FS_Interval DEF CLrn
  <1> QED BY <1>1, <1>2 DEF FiniteLearners
=============================================================================
