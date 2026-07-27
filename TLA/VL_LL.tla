--------------------------------- MODULE VL_LL ---------------------------------
EXTENDS LearnerGraphConcrete

LEMMA VL_LL == \A m \in CLG : \A mx \in CLQ : \A my \in CLQ : (m \cap mx \cap my) # {}
  BY DEF CLG, CLQ
=============================================================================
