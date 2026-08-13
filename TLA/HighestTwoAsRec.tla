------------------------- MODULE HighestTwoAsRec -------------------------
\*   MemoInv -> cited lemma
EXTENDS RecursiveWellFormed, MemoInv

\* Every message's highesttwoas field satisfies its structural invariant:
\* domain = learners attested for in the exclusive history, entries are
\* canonical memos of maximal-ballot attesters. (Corollary of the
\* combined induction MemoInv, which threads the recursive lrns field
\* this assembly reads.)
LEMMA HighestTwoAsRec ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages
  PROVE HighestTwoAsInvariant(m)
BY MemoInv DEF MemoInvariant
====================================================================
