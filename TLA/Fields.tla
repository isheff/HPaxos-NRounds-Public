-------------------------------- MODULE Fields --------------------------------
EXTENDS LearnerGraphConcrete

LEMMA Fields == ASSUME LearnerGraphInterface = CLGI
  PROVE /\ Learners = CLrn /\ Acceptors = CAcc
        /\ SpecifiedSafetySets = CSafety /\ SpecifiedQuorums = CQuorums
  BY DEF Learners, Acceptors, SpecifiedSafetySets, SpecifiedQuorums, CLGI
=============================================================================
