----------------------------- MODULE MemoStep -----------------------------
\*   HighestTwoAsStep, FreshResolve, MaxQDepthStep, LrnsStep, MemoRec
\*     -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, HighestTwoAsStep, FreshResolve, MaxQDepthStep,
        LrnsStep, MemoRec
LOCAL INSTANCE TLAPS

\* The combined inductive step, instantiating the generalized (arbitrary-S)
\* step lemmas at S := Refs(x) and identifying the assemblies with the
\* stored fields via the memo recursion. Order: refs' lrns feed x's
\* highesttwoas; x's highesttwoas (with caught and bal) decides x's fresh;
\* x's fresh supplies the level-0 base of x's frontier; and the frontier
\* decides x's lrns.
LEMMA MemoStep ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW x \in Messages,
         \A p \in Refs(x) : MemoInvariant(p)
  PROVE MemoInvariant(x)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE recs == {Memo(p) : p \in Refs(x)}
<1>rsub. Refs(x) \subseteq TranExclusive(x)  BY DEF Refs
<1>ihHT. \A p \in Refs(x) : HighestTwoAsInvariant(p)
  BY DEF MemoInvariant
<1>ihMQ. \A p \in Refs(x) : MaxQDepthInvariant(p)
  BY DEF MemoInvariant
<1>ihL. \A p \in Refs(x) : MemoLrns(p) = Lrns(p)
  BY DEF MemoInvariant
<1>unf. Memo(x) = MemoR(x, recs)
  BY <1>tok, <1>tt, <1>tf, <1>ta, MemoRec
<1>htA. HighestTwoAsCorrect(x, HighestTwoAsAssemble(recs))
  BY <1>rsub, <1>ihHT, <1>ihL,
     <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, HighestTwoAsStep
<1>ht. HighestTwoAsInvariant(x)
  <2>1. MemoHighestTwoAs(x) = HighestTwoAsAssemble(recs)
    BY <1>unf DEF MemoHighestTwoAs, MemoR
  <2>2. HighestTwoAsCorrect(x, MemoHighestTwoAs(x))  BY <1>htA, <2>1
  <2> QED BY <2>2 DEF HighestTwoAsInvariant, HighestTwoAsCorrect
<1>fr. \A alpha \in Learners :
         FreshAssemble(alpha, x, recs) <=> Fresh(alpha, x)
  <2> SUFFICES ASSUME NEW alpha \in Learners
      PROVE FreshAssemble(alpha, x, recs) <=> Fresh(alpha, x)  OBVIOUS
  <2> QED BY <1>rsub, <1>htA,
            <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, FreshResolve
<1>mq. MaxQDepthInvariant(x)
  <2>1. MaxQDepthCorrect(x, MaxQDepthAssemble(x, recs),
                         PendingQdAssemble(x, recs))
    BY <1>rsub, <1>fr, <1>ihMQ, MaxQDepthStep
  <2>2. MemoMaxQDepth(x) = MaxQDepthAssemble(x, recs)
    BY <1>unf DEF MemoMaxQDepth, MemoR
  <2>3. MemoPendingQd(x) = PendingQdAssemble(x, recs)
    BY <1>unf DEF MemoPendingQd, MemoR
  <2>4. MaxQDepthCorrect(x, MemoMaxQDepth(x), MemoPendingQd(x))
    BY <2>1, <2>2, <2>3
  <2> QED BY <2>4 DEF MaxQDepthInvariant, MaxQDepthCorrect
<1>lr. MemoLrns(x) = Lrns(x)
  <2>1. LrnsAssemble(x, recs) = Lrns(x)
    BY <1>rsub, <1>ihMQ, LrnsStep
  <2>2. MemoLrns(x) = LrnsAssemble(x, recs)
    BY <1>unf DEF MemoLrns, MemoR
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ht, <1>mq, <1>lr DEF MemoInvariant
====================================================================
