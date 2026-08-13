------------------------------ MODULE MemoInv ------------------------------
\*   MemoStep, RefsInduction -> cited lemmas
EXTENDS RecursiveWellFormed, MemoStep, RefsInduction

\* Every message's memo satisfies the combined invariant: highesttwoas
\* and maxqdepth/pendingqd structurally correct, and lrns = Lrns.
LEMMA MemoInv ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW m \in Messages
  PROVE MemoInvariant(m)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>cl. \A x \in Messages :
         (\A y \in Refs(x) : MemoInvariant(y)) => MemoInvariant(x)
  BY MemoStep
<1> QED BY <1>cl, <1>tok, <1>tf, <1>tt, <1>ta, RefsInduction
====================================================================
