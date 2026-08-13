------------------------------- MODULE LrnsRec -------------------------------
\*   MemoInv -> cited lemma
EXTENDS RecursiveWellFormed, MemoInv

\* The recursively-assembled lrns field is exactly Lrns. (Corollary of the
\* combined induction MemoInv.)
LEMMA LrnsRec ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages
  PROVE MemoLrns(m) = Lrns(m)
BY MemoInv DEF MemoInvariant
====================================================================
