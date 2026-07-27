----------------------- MODULE ConcreteQuorumsNonEmpty -----------------------
EXTENDS LearnerGraphConcrete, Fields, QuorumResolve, FiniteSetTheorems

LEMMA ConcreteQuorumsNonEmpty == ASSUME LearnerGraphInterface = CLGI PROVE QuorumsNonEmpty
  <1>L. Learners = CLrn BY Fields
  <1> SUFFICES ASSUME NEW alpha \in Learners PROVE Quorums(alpha) # {}
    BY DEF QuorumsNonEmpty
  <1>1. alpha \in 1..4 BY <1>L DEF CLrn
  <1>2. GetSpecifiedQuorums(alpha) = IF alpha \in {1,2} THEN CLQ ELSE CRQ BY <1>1, QuorumResolve
  <1>3. GetSpecifiedQuorums(alpha) # {}
    <2>1. CLQ # {} BY DEF CLQ
    <2>2. CRQ # {} BY DEF CRQ
    <2> QED BY <1>2, <2>1, <2>2
  <1>4. PICK m \in GetSpecifiedQuorums(alpha) : TRUE BY <1>3
  <1>acc. Acceptors = CAcc BY Fields
  <1>5. m \subseteq Acceptors
    <2>1. m \subseteq CAcc BY <1>2, <1>4 DEF CLQ, CRQ, CAcc
    <2> QED BY <2>1, <1>acc
  <1>6. m \in SUBSET Acceptors BY <1>5
  <1>7. IsFiniteSet(Acceptors)
    <2>1. IsFiniteSet(CAcc) BY FS_Interval DEF CAcc
    <2> QED BY <1>acc, <2>1
  <1>8. m \in Quorums(alpha)
    <2>1. \E mm \in GetSpecifiedQuorums(alpha) : mm \subseteq m BY <1>4
    <2>2. IsFiniteSet(m) BY <1>5, <1>7, FS_Subset
    <2> QED BY <1>6, <2>1, <2>2 DEF Quorums
  <1> QED BY <1>8
=============================================================================
