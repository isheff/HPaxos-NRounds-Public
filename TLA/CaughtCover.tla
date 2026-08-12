------------------------------ MODULE CaughtCover ------------------------------
\*   CaughtStep, CaughtRec, TranSubMessages -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, CaughtStep, CaughtRec, TranSubMessages
LOCAL INSTANCE TLAPS

\* The caught assembly over the digests of ANY set between Refs(x) and
\* TranExclusive(x) equals Caught(x).
LEMMA CaughtCover ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x)
  PROVE CaughtAssemble({Digest(p) : p \in S}) = Caught(x)
<1>1. S \subseteq Messages  BY TranSubMessages DEF TranExclusive
<1>2. \A p \in S : DigestCaught(p) = Caught(p)  BY <1>1, CaughtRec
<1> QED BY <1>2, CaughtStep
====================================================================
