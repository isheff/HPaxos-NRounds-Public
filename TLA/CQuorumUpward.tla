----------------------------- MODULE CQuorumUpward -----------------------------
EXTENDS MessageConcrete

\* Quorums are upward-closed within finite subsets of Acceptors.
LEMMA CQuorumUpward ==
  ASSUME NEW l \in Learners, NEW s, NEW t,
         s \in Quorums(l), s \subseteq t, t \subseteq Acceptors, IsFiniteSet(t)
  PROVE t \in Quorums(l)
<1>1. \E mm \in GetSpecifiedQuorums(l) : mm \subseteq s  BY DEF Quorums
<1>2. \E mm \in GetSpecifiedQuorums(l) : mm \subseteq t  BY <1>1
<1> QED BY <1>2 DEF Quorums
=============================================================================
