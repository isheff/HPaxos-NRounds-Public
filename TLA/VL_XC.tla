--------------------------------- MODULE VL_XC ---------------------------------
EXTENDS LearnerGraphConcrete

LEMMA VL_XC == \A m \in CCG : \A mx \in CRQ : \A my \in CLQ : (m \cap mx \cap my) # {}
  BY DEF CCG, CRQ, CLQ
=============================================================================
