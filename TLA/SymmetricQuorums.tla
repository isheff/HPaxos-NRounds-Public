---------------------------- MODULE SymmetricQuorums ----------------------------
\* Symmetric (Byzantine) quorum systems, as targeted by the quorum compilers
\* of "Symmetry All the Way Down" (Definition 4.2): a single quorum system S
\* tolerates a family FF of failure patterns when its quorums pairwise
\* intersect outside every pattern (consistency) and some quorum avoids each
\* pattern (availability).  Definitions only; the impossibility lives in
\* NoSymmetricQuorumF1.
SymConsistency(S, FF) ==
  \A q1 \in S : \A q2 \in S : \A f \in FF : ~((q1 \cap q2) \subseteq f)

SymAvailability(S, FF) ==
  \A f \in FF : \E q \in S : q \cap f = {}
====================================================================
