---------------------------- MODULE MaxQDepthInv ----------------------------
\*   DigestInv -> cited lemma
EXTENDS RecursiveWellFormed, DigestInv

\* Every message's maxqdepth/pendingqd fields satisfy the accumulator
\* invariant: domain = learners with a same-ballot attester in the
\* inclusive history, frontier attained and maximal, pending = the
\* frontier attesters. (Corollary of the combined induction DigestInv.)
LEMMA MaxQDepthInv ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages
  PROVE MaxQDepthInvariant(m)
BY DigestInv DEF DigestInvariant
====================================================================
