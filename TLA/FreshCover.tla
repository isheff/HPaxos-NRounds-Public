------------------------------ MODULE FreshCover ------------------------------
\*   FreshResolve, HighestTwoAsCover -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, FreshResolve, HighestTwoAsCover
LOCAL INSTANCE TLAPS

\* The fresh check over the memos of ANY set between Refs(x) and
\* TranExclusive(x) decides Fresh exactly.
LEMMA FreshCover ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW x \in Messages,
         NEW S, Refs(x) \subseteq S, S \subseteq TranExclusive(x),
         NEW alpha \in Learners
  PROVE FreshAssemble(alpha, x, {Memo(p) : p \in S}) <=> Fresh(alpha, x)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>1. HighestTwoAsCorrect(x, HighestTwoAsAssemble({Memo(p) : p \in S}))
  BY HighestTwoAsCover
<1> QED BY <1>1, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, FreshResolve
====================================================================
