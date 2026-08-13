---------------------------- MODULE MaxQDepthInv ----------------------------
\*   MemoInv -> cited lemma
EXTENDS RecursiveWellFormed, MemoInv

\* Every message's maxqdepth/pendingqd fields satisfy the accumulator
\* invariant: domain = learners with a same-ballot attester in the
\* inclusive history, frontier attained and maximal, pending = the
\* frontier attesters. (Corollary of the combined induction MemoInv.)
LEMMA MaxQDepthInv ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages
  PROVE MaxQDepthInvariant(m)
BY MemoInv DEF MemoInvariant
====================================================================
