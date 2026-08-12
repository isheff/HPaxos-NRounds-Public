------------------------- MODULE HighestTwoAsRec -------------------------
\*   DigestInv -> cited lemma
EXTENDS RecursiveWellFormed, DigestInv

\* Every message's highesttwoas field satisfies its structural invariant:
\* domain = learners attested for in the exclusive history, entries are
\* canonical digests of maximal-ballot attesters. (Corollary of the
\* combined induction DigestInv, which threads the recursive lrns field
\* this assembly reads.)
LEMMA HighestTwoAsRec ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages
  PROVE HighestTwoAsInvariant(m)
BY DigestInv DEF DigestInvariant
====================================================================
