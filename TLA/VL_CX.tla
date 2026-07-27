--------------------------------- MODULE VL_CX ---------------------------------
EXTENDS LearnerGraphConcrete

LEMMA VL_CX == \A m \in CCG : \A mx \in CLQ : \A my \in CRQ : (m \cap mx \cap my) # {}
  BY DEF CCG, CLQ, CRQ
=============================================================================
