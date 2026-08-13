------------------------------- MODULE LrnsCover -------------------------------
\*   LrnsStep, MaxQDepthInv, TranSubMessages -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, LrnsStep, MaxQDepthInv, TranSubMessages
LOCAL INSTANCE TLAPS

\* The lrns assembly over the memos of ANY set between Refs(x) and
\* TranExclusive(x) equals Lrns(x).
LEMMA LrnsCover ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x)
  PROVE LrnsAssemble(x, {Memo(p) : p \in S}) = Lrns(x)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>1. S \subseteq Messages
  BY <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>2. \A p \in S : MaxQDepthInvariant(p)  BY <1>1, MaxQDepthInv
<1> QED BY <1>2, LrnsStep
====================================================================
