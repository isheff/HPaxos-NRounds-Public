---------------------------- MODULE MaxQDepthCover ----------------------------
\*   MaxQDepthStep, MaxQDepthInv, FreshCover, TranSubMessages -> cited
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, MaxQDepthStep, MaxQDepthInv, FreshCover,
        TranSubMessages
LOCAL INSTANCE TLAPS

\* The maxqdepth/pendingqd assembly over the digests of ANY set between
\* Refs(x) and TranExclusive(x) is a correct accumulator for x.
LEMMA MaxQDepthCover ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x)
  PROVE MaxQDepthCorrect(x, MaxQDepthAssemble(x, {Digest(p) : p \in S}),
                         PendingQdAssemble(x, {Digest(p) : p \in S}))
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>1. S \subseteq Messages
  BY <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>2. \A p \in S : MaxQDepthInvariant(p)  BY <1>1, MaxQDepthInv
<1>3. \A alpha \in Learners :
        FreshAssemble(alpha, x, {Digest(p) : p \in S}) <=> Fresh(alpha, x)
  BY FreshCover
<1> QED BY <1>2, <1>3, MaxQDepthStep
====================================================================
