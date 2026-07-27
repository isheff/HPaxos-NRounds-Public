--------------------------------- MODULE VL_RR ---------------------------------
EXTENDS LearnerGraphConcrete

LEMMA VL_RR == \A m \in CRG : \A mx \in CRQ : \A my \in CRQ : (m \cap mx \cap my) # {}
  BY DEF CRG, CRQ
=============================================================================
