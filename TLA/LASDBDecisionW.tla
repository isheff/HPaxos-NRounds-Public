---------------------------- MODULE LASDBDecisionW ----------------------------
EXTENDS HPaxosPlusCal, LiveAcceptorsSentDepthBallotDecision

\* Opaque-operator wrapper for LiveAcceptorsSentDepthBallotDecision so it can be
\* applied at b := B(p) (a non-identity instantiation of a temporal conclusion,
\* which fails directly -- tlaps skill sec.10 / wall #8).
LEMMA LASDBDecisionW ==
  ASSUME MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions,
         AcceptorsAssumptions,
         NEW alpha \in Learners, NEW allmessages \in SUBSET Messages, NEW b \in Ballots,
         LiveAcceptors \in Quorums(alpha),
         LiveAcceptorsSentDepthBallot(allmessages, alpha, b, MaxDepth(alpha))
  PROVE  LASDBDecOp(alpha, allmessages, b)
BY LiveAcceptorsSentDepthBallotDecision DEF LASDBDecOp
====================================================================
