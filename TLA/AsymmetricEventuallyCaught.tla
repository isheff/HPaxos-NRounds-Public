------------------------ MODULE AsymmetricEventuallyCaught ------------------------
\* Accountability over an arbitrary B^3 asymmetric quorum system.  Note the
\* guarantee needs NO wisdom, quorum, or safety-set hypothesis whatsoever:
\* detection of equivocation is in the self-verifiable fragment -- with
\* authentication, even an acceptor whose every trust assumption is wrong
\* (depth zero) eventually holds proof of the equivocator's guilt, as long as
\* the two fork witnesses reach live acceptors.
EXTENDS HPaxosPlusCal, AsymmetricQuorums, AQSupportsAssumptions, EventuallyCaught
LOCAL INSTANCE TLAPS

THEOREM AsymmetricEventuallyCaught ==
  ASSUME MessageInterfaceAssumptions, AcceptorsAssumptions,
         NEW fps, AQTypeOK(fps), AQNonTrivial(fps), AQB3(fps), AQEmbedded(fps),
         IsFiniteSet(Acceptors), Acceptors # {},
         NEW x \in Acceptors, NEW m1 \in Messages, NEW m2 \in Messages,
         Sig(m1) = x, Sig(m2) = x,
         m1 \notin Tran(m2), m2 \notin Tran(m1)
  PROVE  (Spec /\ NetworkAssumption) =>
           ((KnownToLive(m1) /\ KnownToLive(m2))
             ~> (\A y \in LiveAcceptors : x \in CaughtS(known_messages[y])))
<1>lga. LearnerGraphAssumptions  BY AQSupportsAssumptions
<1> QED  BY <1>lga, EventuallyCaught
====================================================================
