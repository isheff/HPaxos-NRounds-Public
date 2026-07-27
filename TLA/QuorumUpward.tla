--------------------------- MODULE QuorumUpward ---------------------------
EXTENDS MessageInterface

\* Quorums are upward-closed within finite subsets of Acceptors (abstract
\* analogue of MessageConcrete's CQuorumUpward -- same proof, since Quorums
\* is the same LearnerGraphInterface operator in both worlds).
LEMMA QuorumUpward ==
  ASSUME NEW l \in Learners, NEW s, NEW t,
         s \in Quorums(l), s \subseteq t, t \subseteq Acceptors, IsFiniteSet(t)
  PROVE t \in Quorums(l)
<1>1. \E mm \in GetSpecifiedQuorums(l) : mm \subseteq s  BY DEF Quorums
<1>2. \E mm \in GetSpecifiedQuorums(l) : mm \subseteq t  BY <1>1
<1> QED BY <1>2 DEF Quorums
====================================================================
