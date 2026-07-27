-------------------------- MODULE ConcreteSafetyType --------------------------
EXTENDS LearnerGraphConcrete, Fields

LEMMA ConcreteSafetyType == ASSUME LearnerGraphInterface = CLGI PROVE SafetySetsTypeOK
  <1>1. SpecifiedSafetySets = CSafety /\ Acceptors = CAcc BY Fields
  <1>2. Learners = CLrn BY Fields
  <1>3. LearnerPairs = CPairs BY <1>2 DEF LearnerPairs, CPairs
  <1>4. \A p \in CPairs : CSafety[p] \in SUBSET (SUBSET CAcc)
    <2>1. CLG \in SUBSET (SUBSET CAcc) /\ CRG \in SUBSET (SUBSET CAcc) /\ CCG \in SUBSET (SUBSET CAcc)
      BY DEF CLG, CRG, CCG, CAcc
    <2> QED BY <2>1 DEF CSafety
  <1>5. CSafety \in [CPairs -> SUBSET (SUBSET CAcc)] BY <1>4 DEF CSafety
  <1> QED BY <1>1, <1>3, <1>5 DEF SafetySetsTypeOK
=============================================================================
