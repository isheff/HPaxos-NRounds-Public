----------------------- MODULE ConcreteLearnersNonEmpty -----------------------
EXTENDS LearnerGraphConcrete, Fields

LEMMA ConcreteLearnersNonEmpty == ASSUME LearnerGraphInterface = CLGI PROVE LearnersNonEmpty
  <1>1. Learners = CLrn BY Fields
  <1>2. CLrn # {} BY DEF CLrn
  <1> QED BY <1>1, <1>2 DEF LearnersNonEmpty
=============================================================================
