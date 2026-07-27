------------------------ MODULE ConcreteFiniteAcceptors ------------------------
\* FiniteSetTheorems by EXTENDS (never LOCAL INSTANCE) so FS_Interval's IsFiniteSet
\* is the same one FiniteAcceptors unfolds to.
EXTENDS LearnerGraphConcrete, Fields, FiniteSetTheorems

LEMMA ConcreteFiniteAcceptors == ASSUME LearnerGraphInterface = CLGI PROVE FiniteAcceptors
  <1>1. Acceptors = CAcc BY Fields
  <1>2. IsFiniteSet(CAcc) BY FS_Interval DEF CAcc
  <1> QED BY <1>1, <1>2 DEF FiniteAcceptors
=============================================================================
