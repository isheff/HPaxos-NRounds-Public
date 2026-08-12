----------------------------- MODULE DigestStep -----------------------------
\*   HighestTwoAsStep, FreshResolve, MaxQDepthStep, LrnsStep, DigestRec
\*     -> cited lemmas
\*   TLAPS -> proof-only
EXTENDS RecursiveWellFormed, HighestTwoAsStep, FreshResolve, MaxQDepthStep,
        LrnsStep, DigestRec
LOCAL INSTANCE TLAPS

\* The combined inductive step, instantiating the generalized (arbitrary-S)
\* step lemmas at S := Refs(x) and identifying the assemblies with the
\* stored fields via the digest recursion. Order: refs' lrns feed x's
\* highesttwoas; x's highesttwoas (with caught and bal) decides x's fresh;
\* x's fresh supplies the level-0 base of x's frontier; and the frontier
\* decides x's lrns.
LEMMA DigestStep ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW x \in Messages,
         \A p \in Refs(x) : DigestInvariant(p)
  PROVE DigestInvariant(x)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1> DEFINE recs == {Digest(p) : p \in Refs(x)}
<1>rsub. Refs(x) \subseteq TranExclusive(x)  BY DEF Refs
<1>ihHT. \A p \in Refs(x) : HighestTwoAsInvariant(p)
  BY DEF DigestInvariant
<1>ihMQ. \A p \in Refs(x) : MaxQDepthInvariant(p)
  BY DEF DigestInvariant
<1>ihL. \A p \in Refs(x) : DigestLrns(p) = Lrns(p)
  BY DEF DigestInvariant
<1>unf. Digest(x) = DigestR(x, recs)
  BY <1>tok, <1>tt, <1>tf, <1>ta, DigestRec
<1>htA. HighestTwoAsCorrect(x, HighestTwoAsAssemble(recs))
  BY <1>rsub, <1>ihHT, <1>ihL,
     <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, HighestTwoAsStep
<1>ht. HighestTwoAsInvariant(x)
  <2>1. DigestHighestTwoAs(x) = HighestTwoAsAssemble(recs)
    BY <1>unf DEF DigestHighestTwoAs, DigestR
  <2>2. HighestTwoAsCorrect(x, DigestHighestTwoAs(x))  BY <1>htA, <2>1
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
  <2>2. DigestMaxQDepth(x) = MaxQDepthAssemble(x, recs)
    BY <1>unf DEF DigestMaxQDepth, DigestR
  <2>3. DigestPendingQd(x) = PendingQdAssemble(x, recs)
    BY <1>unf DEF DigestPendingQd, DigestR
  <2>4. MaxQDepthCorrect(x, DigestMaxQDepth(x), DigestPendingQd(x))
    BY <2>1, <2>2, <2>3
  <2> QED BY <2>4 DEF MaxQDepthInvariant, MaxQDepthCorrect
<1>lr. DigestLrns(x) = Lrns(x)
  <2>1. LrnsAssemble(x, recs) = Lrns(x)
    BY <1>rsub, <1>ihMQ, LrnsStep
  <2>2. DigestLrns(x) = LrnsAssemble(x, recs)
    BY <1>unf DEF DigestLrns, DigestR
  <2> QED BY <2>1, <2>2
<1> QED BY <1>ht, <1>mq, <1>lr DEF DigestInvariant
====================================================================
