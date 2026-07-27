-------------------------- MODULE ConcreteQuorumType --------------------------
EXTENDS LearnerGraphConcrete, Fields

LEMMA ConcreteQuorumType == ASSUME LearnerGraphInterface = CLGI PROVE QuorumsTypeOK
  <1>1. SpecifiedQuorums = CQuorums /\ Acceptors = CAcc /\ Learners = CLrn BY Fields
  <1>2. \A l \in CLrn : CQuorums[l] \in SUBSET (SUBSET CAcc)
    <2>1. CLQ \in SUBSET (SUBSET CAcc) /\ CRQ \in SUBSET (SUBSET CAcc)
      BY DEF CLQ, CRQ, CAcc
    <2> QED BY <2>1 DEF CQuorums
  <1>3. CQuorums \in [CLrn -> SUBSET (SUBSET CAcc)] BY <1>2 DEF CQuorums
  <1> QED BY <1>1, <1>3 DEF QuorumsTypeOK
=============================================================================
