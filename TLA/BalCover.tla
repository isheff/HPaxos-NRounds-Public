------------------------------- MODULE BalCover -------------------------------
\*   BalStep, BalRec, TranSubMessages -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, BalStep, BalRec, TranSubMessages
LOCAL INSTANCE TLAPS

\* The bal assembly over the memos of ANY set between Refs(x) and
\* TranExclusive(x) equals B(x).
LEMMA BalCover ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         AlwaysAProposal,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x)
  PROVE BalAssemble(x, {Memo(p) : p \in S}) = B(x)
<1>1. S \subseteq Messages  BY TranSubMessages DEF TranExclusive
<1>2. \A p \in S : MemoBal(p) = B(p)  BY <1>1, BalRec
<1> QED BY <1>2, BalStep
====================================================================
