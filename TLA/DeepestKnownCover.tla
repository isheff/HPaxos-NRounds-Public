------------------------- MODULE DeepestKnownCover -------------------------
\*   DeepestKnownStep, DeepestKnownInv, TranSubMessages -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, DeepestKnownStep, DeepestKnownInv,
        TranSubMessages
LOCAL INSTANCE TLAPS

\* The deepestknown assembly over the digests of ANY set between Refs(x)
\* and TranExclusive(x) is correct for x (member invariants come from the
\* proven per-message invariant).
LEMMA DeepestKnownCover ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x)
  PROVE DeepestKnownCorrect(x, DeepestKnownAssemble({Digest(p) : p \in S}))
<1>1. S \subseteq Messages  BY TranSubMessages DEF TranExclusive
<1>2. \A p \in S : DeepestKnownInvariant(p)  BY <1>1, DeepestKnownInv
<1> QED BY <1>2, DeepestKnownStep
====================================================================
