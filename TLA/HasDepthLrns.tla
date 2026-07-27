--------------------------- MODULE HasDepthLrns ---------------------------
EXTENDS MessageInterface, HasDepthDownward

\* Any positive depth registers the learner in Lrns.
LEMMA HasDepthLrns ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW d \in Nat, d >= 1,
         HasDepth(alpha, x, d)
  PROVE alpha \in Lrns(x)
<1>1. HasDepth(alpha, x, 1)  BY HasDepthDownward
<1> QED BY <1>1 DEF Lrns
====================================================================
