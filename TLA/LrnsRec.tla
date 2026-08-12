------------------------------- MODULE LrnsRec -------------------------------
\*   DigestInv -> cited lemma
EXTENDS RecursiveWellFormed, DigestInv

\* The recursively-assembled lrns field is exactly Lrns. (Corollary of the
\* combined induction DigestInv.)
LEMMA LrnsRec ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages
  PROVE DigestLrns(m) = Lrns(m)
BY DigestInv DEF DigestInvariant
====================================================================
