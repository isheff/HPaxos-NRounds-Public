--------------------------- MODULE HighestTwoAsCover ---------------------------
\*   HighestTwoAsStep, HighestTwoAsRec, LrnsRec, TranSubMessages -> cited
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, HighestTwoAsStep, HighestTwoAsRec, LrnsRec,
        TranSubMessages
LOCAL INSTANCE TLAPS

\* The highesttwoas assembly over the digests of ANY set between Refs(x)
\* and TranExclusive(x) is correct for x.
LEMMA HighestTwoAsCover ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x)
  PROVE HighestTwoAsCorrect(x, HighestTwoAsAssemble({Digest(p) : p \in S}))
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>1. S \subseteq Messages
  BY <1>tok, <1>tt, TranSubMessages DEF TranExclusive
<1>2. \A p \in S : HighestTwoAsInvariant(p)  BY <1>1, HighestTwoAsRec
<1>3. \A p \in S : DigestLrns(p) = Lrns(p)  BY <1>1, LrnsRec
<1> QED BY <1>2, <1>3,
          <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, HighestTwoAsStep
====================================================================
