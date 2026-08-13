------------------------------ MODULE MemoPGoodInv ------------------------------
\* Every real message's priors-recursive memo is good: MemoP stores exactly
\* the data the candidate check reads, with the semantic meanings the
\* refs-recursive Memo has.  One course-of-values induction over the
\* concrete strict closure (CTranExclInduction) with the six assembly legs:
\* S1 bal/newbal, S2 highesttwoas, S3 lrns + frontier, S4 deepestknown,
\* S5 caught, S6 the prevtran chain.  MemoPRec turns MemoP(x) into the
\* assembly over the priors' MemoP records, which is what every leg speaks
\* about (S6 already speaks about MemoP(x) itself).
EXTENDS MemoPDefs, MemoPRec, CTranExclInduction, CMessagesSubMC,
        MemoPBalStep, MemoPHTStep, MemoPDKStep, MemoPCaughtStep,
        MemoPPrevStep, MemoPLrnsMQStep
LOCAL INSTANCE TLAPS

LEMMA MemoPGoodInv ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         MessageInterface = CMI,
         NEW m \in CMessages
  PROVE MemoPGood(m)
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>cl. \A x \in CMessages :
         (\A y \in CTranExcl(x) : MemoPGood(y)) => MemoPGood(x)
  <2> SUFFICES ASSUME NEW x \in CMessages,
                      \A y \in CTranExcl(x) : MemoPGood(y)
      PROVE MemoPGood(x)
    OBVIOUS
  <2> DEFINE pr == x.priors
  <2> DEFINE rP == {MemoP(q) : q \in pr}
  <2>unf. MemoP(x) = MemoR(x, rP)
    <3>1. x \in CMC  BY CMessagesSubMC
    <3>2. CPriors(x) = pr  BY DEF CPriors
    <3> QED BY <3>1, <3>2, MemoPRec
  <2>id. MemoP(x).id = x  BY <2>unf DEF MemoR
  <2>bal. /\ MemoP(x).bal = B(x)
          /\ (MemoP(x).newbal <=> (\A y \in Refs(x) : B(y) < B(x)))
    <3>1. /\ BalAssemble(x, rP) = B(x)
          /\ (NewBalAssemble(x, rP) <=> (\A y \in Refs(x) : B(y) < B(x)))
      BY <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, MemoPBalStep
    <3> QED BY <3>1, <2>unf DEF MemoR
  <2>caught. MemoP(x).caught = Caught(x)
    <3>1. CaughtAssemble(rP) = Caught(x)
      BY <1>tok, <1>tt, <1>tf, <1>ta, MemoPCaughtStep
    <3> QED BY <3>1, <2>unf DEF MemoR
  <2>lrnsmq. /\ MemoP(x).lrns = Lrns(x)
             /\ MaxQDepthCorrect(x, MemoP(x).maxqdepth, MemoP(x).pendingqd)
    <3>1. /\ LrnsAssemble(x, rP) = Lrns(x)
          /\ MaxQDepthCorrect(x, MaxQDepthAssemble(x, rP),
                              PendingQdAssemble(x, rP))
      BY MemoPLrnsMQStep
    <3> QED BY <3>1, <2>unf DEF MemoR
  <2>ht. /\ DOMAIN MemoP(x).highesttwoas
              = {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
         /\ \A l \in DOMAIN MemoP(x).highesttwoas :
              /\ \E y \in TranExclusive(x) :
                   l \in Lrns(y) /\ B(y) = MemoP(x).highesttwoas[l].bal
              /\ \A y \in TranExclusive(x) :
                   l \in Lrns(y) => B(y) <= MemoP(x).highesttwoas[l].bal
    <3>1. /\ DOMAIN HighestTwoAsAssemble(rP)
               = {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
          /\ \A l \in DOMAIN HighestTwoAsAssemble(rP) :
               /\ \E y \in TranExclusive(x) :
                    l \in Lrns(y)
                    /\ B(y) = HighestTwoAsAssemble(rP)[l].bal
               /\ \A y \in TranExclusive(x) :
                    l \in Lrns(y) => B(y) <= HighestTwoAsAssemble(rP)[l].bal
      BY <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, MemoPHTStep
    <3>2. MemoP(x).highesttwoas = HighestTwoAsAssemble(rP)
      BY <2>unf DEF MemoR
    <3> QED BY <3>1, <3>2
  <2>dk. DeepestKnownCorrectP(x, MemoP(x).deepestknown)
    <3>1. DeepestKnownCorrectP(x, DeepestKnownAssemble(rP))
      BY <1>tok, <1>tt, <1>tf, <1>ta, MemoPDKStep
    <3>2. MemoP(x).deepestknown = DeepestKnownAssemble(rP)
      BY <2>unf DEF MemoR
    <3> QED BY <3>1, <3>2
  <2>prev. /\ x \in MemoP(x).prevtran
           /\ MemoP(x).prevtran \subseteq Tran(x)
           /\ \A y \in MemoP(x).prevtran : Sig(y) = Sig(x)
           /\ \A y \in MemoP(x).prevtran :
                MemoP(y).prevtran \subseteq MemoP(x).prevtran
           /\ \A y1 \in MemoP(x).prevtran : \A y2 \in MemoP(x).prevtran :
                y1 \in Tran(y2) \/ y2 \in Tran(y1)
           /\ (Sig(x) \in Acceptors =>
                 \A y \in TranExclusive(x) :
                   (Sig(y) = Sig(x) /\ y \notin MemoP(x).prevtran)
                     => Sig(x) \in Caught(x))
           /\ \A y \in TranExclusive(x) :
                (Sig(y) \in Acceptors /\ Sig(y) \notin Caught(x)) =>
                  /\ Sig(y) \in DOMAIN MemoP(x).deepestknown
                  /\ y \in MemoP(x).deepestknown[Sig(y)][2].prevtran
    BY <1>tok, <1>tt, <1>tf, <1>ta, MemoPPrevStep
  <2> QED BY <2>id, <2>bal, <2>caught, <2>lrnsmq, <2>ht, <2>dk, <2>prev
    DEF MemoPGood
<1> QED BY <1>cl, CTranExclInduction
=============================================================================
