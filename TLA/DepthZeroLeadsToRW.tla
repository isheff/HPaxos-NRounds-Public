------------------------- MODULE DepthZeroLeadsToRW -------------------------
EXTENDS HPaxosPlusCal, DepthZeroLeadsToR

\* Thin wrapper for DepthZeroLeadsToR over the opaque hypothesis bundle.
LEMMA DepthZeroLeadsToRW ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions, ValueInterfaceAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         NEW p \in Proposals, NEW am \in SUBSET Messages, NEW a \in LiveAcceptors,
         DZLTHypR(alpha, bal, m, p, am)
  PROVE (Spec /\ TranFairness(p)) =>
        ((p \in Msgs) ~> (\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)))
BY DepthZeroLeadsToR DEF DZLTHypR
====================================================================
