---------------------------- MODULE MemoPLrnsMQStep ----------------------------
\* MemoP tower, leg S3: the lrns and maxqdepth/pendingqd assemblies over the
\* priors' MemoP records are correct.
\*
\* These three assemblies read the members through the frontier operators
\* (SBRefs / QDom / RefFrontier / RefPending / Bump) and through x's own
\* level-0 test SelfL0, which in turn reads the caught, highesttwoas and bal
\* assemblies.  Every one of those reads is value-determined, so the whole
\* P-side assembly EQUALS the canonical one over {Memo(q) : q \in priors}
\* -- and that one is handled by LrnsCover / MaxQDepthCover at S := priors.
\* The record-level facts come from MemoPFields (members) and from S1 / S2 /
\* S5 (the bal, highesttwoas-in-projection and caught assemblies).
EXTENDS MemoPDefs, MemoPFields, MemoPBalStep, MemoPHTStep, MemoPCaughtStep,
        BalCover, CaughtCover, HighestTwoAsCover, LrnsCover, MaxQDepthCover,
        BalRec, BBallot, MemoRec, CRefsSubPriors, TranSubMessages,
        CFields, CMessageTranClosed, CTranResolve
LOCAL INSTANCE TLAPS

LEMMA MemoPLrnsMQStep ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         MessageInterface = CMI,
         NEW x \in CMessages,
         \A y \in CTranExcl(x) : MemoPGood(y)
  PROVE /\ LrnsAssemble(x, {MemoP(q) : q \in x.priors}) = Lrns(x)
        /\ MaxQDepthCorrect(x,
             MaxQDepthAssemble(x, {MemoP(q) : q \in x.priors}),
             PendingQdAssemble(x, {MemoP(q) : q \in x.priors}))
<1> DEFINE pr == x.priors
<1> DEFINE rP == {MemoP(q) : q \in pr}
<1> DEFINE rC == {Memo(q) : q \in pr}
\* ------------------------------------------------------------------ prelude
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>xm. x \in Messages  BY CFields
<1>sand. Refs(x) \subseteq pr /\ pr \subseteq TranExclusive(x)
  BY CRefsSubPriors
<1>teq. TranExclusive(x) = CTranExcl(x)
  <2>1. Tran(x) = CTran(x)  BY CTranResolve
  <2> QED BY <2>1 DEF TranExclusive, CTranExcl
<1>ihq. \A q \in pr : MemoPGood(q)  BY <1>sand, <1>teq
<1>teM. TranExclusive(x) \subseteq Messages
  BY <1>xm, <1>tok, TranSubMessages DEF TranExclusive
<1>prMsg. pr \subseteq Messages  BY <1>sand, <1>teM
\* ------------------------------------------------------- member projections
<1>midp. \A q \in pr : Memo(q).id = q
  <2> SUFFICES ASSUME NEW q \in pr PROVE Memo(q).id = q  OBVIOUS
  <2>1. q \in Messages  BY <1>prMsg
  <2>2. Memo(q) = MemoR(q, {Memo(z) : z \in Refs(q)})
    BY <2>1, <1>tok, <1>tt, <1>tf, <1>ta, MemoRec
  <2> QED BY <2>2 DEF MemoR
<1>flds. \A q \in pr :
           /\ MemoP(q).id = Memo(q).id
           /\ MemoP(q).bal = Memo(q).bal
           /\ (MemoP(q).newbal <=> Memo(q).newbal)
           /\ DOMAIN MemoP(q).maxqdepth = DOMAIN Memo(q).maxqdepth
           /\ \A alpha \in DOMAIN MemoP(q).maxqdepth :
                /\ MemoP(q).maxqdepth[alpha] = Memo(q).maxqdepth[alpha]
                /\ MemoP(q).pendingqd[alpha] = Memo(q).pendingqd[alpha]
  <2> SUFFICES ASSUME NEW q \in pr
      PROVE /\ MemoP(q).id = Memo(q).id
            /\ MemoP(q).bal = Memo(q).bal
            /\ (MemoP(q).newbal <=> Memo(q).newbal)
            /\ DOMAIN MemoP(q).maxqdepth = DOMAIN Memo(q).maxqdepth
            /\ \A alpha \in DOMAIN MemoP(q).maxqdepth :
                 /\ MemoP(q).maxqdepth[alpha] = Memo(q).maxqdepth[alpha]
                 /\ MemoP(q).pendingqd[alpha] = Memo(q).pendingqd[alpha]
    OBVIOUS
  <2>1. q \in Messages  BY <1>prMsg
  <2>2. MemoPGood(q)  BY <1>ihq
  <2>3. /\ MemoP(q).id = q
        /\ MemoP(q).bal = Memo(q).bal
        /\ (MemoP(q).newbal <=> Memo(q).newbal)
        /\ DOMAIN MemoP(q).maxqdepth = DOMAIN Memo(q).maxqdepth
        /\ \A alpha \in DOMAIN MemoP(q).maxqdepth :
             /\ MemoP(q).maxqdepth[alpha] = Memo(q).maxqdepth[alpha]
             /\ MemoP(q).pendingqd[alpha] = Memo(q).pendingqd[alpha]
    BY <2>1, <2>2, MemoPFields
  <2> QED BY <2>3, <1>midp
\* ------------------------------------------------------------ bal assemblies
<1>balP. BalAssemble(x, rP) = B(x)
  BY <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, MemoPBalStep
<1>balC. BalAssemble(x, rC) = B(x)
  BY <1>xm, <1>sand, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalCover
<1>baleq. BalAssemble(x, rP) = BalAssemble(x, rC)  BY <1>balP, <1>balC
\* -------------------------------------------------------- same-ballot refs
<1> DEFINE SB == {q \in pr : Memo(q).bal = BalAssemble(x, rC)}
<1>sbP. SBRefs(x, rP) = {MemoP(q) : q \in SB}
  <2>sub. SBRefs(x, rP) \subseteq {MemoP(q) : q \in SB}
    <3> SUFFICES ASSUME NEW rc \in SBRefs(x, rP)
        PROVE rc \in {MemoP(q) : q \in SB}  OBVIOUS
    <3>1. rc \in rP /\ rc.bal = BalAssemble(x, rP)  BY DEF SBRefs
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3>3. Memo(q).bal = BalAssemble(x, rC)
      BY <3>1, <3>2, <1>flds, <1>baleq
    <3> QED BY <3>2, <3>3
  <2>sup. {MemoP(q) : q \in SB} \subseteq SBRefs(x, rP)
    <3> SUFFICES ASSUME NEW q \in SB
        PROVE MemoP(q) \in SBRefs(x, rP)  OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3>2. MemoP(q).bal = BalAssemble(x, rP)
      BY <1>flds, <1>baleq
    <3> QED BY <3>1, <3>2 DEF SBRefs
  <2> QED BY <2>sub, <2>sup
<1>sbC. SBRefs(x, rC) = {Memo(q) : q \in SB}
  <2>sub. SBRefs(x, rC) \subseteq {Memo(q) : q \in SB}
    <3> SUFFICES ASSUME NEW rc \in SBRefs(x, rC)
        PROVE rc \in {Memo(q) : q \in SB}  OBVIOUS
    <3>1. rc \in rC /\ rc.bal = BalAssemble(x, rC)  BY DEF SBRefs
    <3>2. PICK q \in pr : rc = Memo(q)  BY <3>1
    <3> QED BY <3>1, <3>2
  <2>sup. {Memo(q) : q \in SB} \subseteq SBRefs(x, rC)
    <3> SUFFICES ASSUME NEW q \in SB
        PROVE Memo(q) \in SBRefs(x, rC)  OBVIOUS
    <3>1. Memo(q) \in rC  OBVIOUS
    <3> QED BY <3>1 DEF SBRefs
  <2> QED BY <2>sub, <2>sup
\* -------------------------------------------------------- frontier operators
<1>qdom. QDom(x, rP) = QDom(x, rC)
  <2>sub. QDom(x, rP) \subseteq QDom(x, rC)
    <3> SUFFICES ASSUME NEW alpha \in QDom(x, rP)
        PROVE alpha \in QDom(x, rC)  OBVIOUS
    <3>1. alpha \in Learners  BY DEF QDom
    <3>2. PICK rc \in SBRefs(x, rP) : alpha \in DOMAIN rc.maxqdepth
      BY DEF QDom
    <3>3. PICK q \in SB : rc = MemoP(q)  BY <3>2, <1>sbP
    <3>4. alpha \in DOMAIN Memo(q).maxqdepth  BY <3>2, <3>3, <1>flds
    <3>5. Memo(q) \in SBRefs(x, rC)  BY <1>sbC
    <3> QED BY <3>1, <3>4, <3>5 DEF QDom
  <2>sup. QDom(x, rC) \subseteq QDom(x, rP)
    <3> SUFFICES ASSUME NEW alpha \in QDom(x, rC)
        PROVE alpha \in QDom(x, rP)  OBVIOUS
    <3>1. alpha \in Learners  BY DEF QDom
    <3>2. PICK rc \in SBRefs(x, rC) : alpha \in DOMAIN rc.maxqdepth
      BY DEF QDom
    <3>3. PICK q \in SB : rc = Memo(q)  BY <3>2, <1>sbC
    <3>4. alpha \in DOMAIN MemoP(q).maxqdepth  BY <3>2, <3>3, <1>flds
    <3>5. MemoP(q) \in SBRefs(x, rP)  BY <1>sbP
    <3> QED BY <3>1, <3>4, <3>5 DEF QDom
  <2> QED BY <2>sub, <2>sup
<1>qcands. \A alpha : QDepthCands(alpha, x, rP) = QDepthCands(alpha, x, rC)
  <2> SUFFICES ASSUME NEW alpha
      PROVE QDepthCands(alpha, x, rP) = QDepthCands(alpha, x, rC)
    OBVIOUS
  <2>sub. QDepthCands(alpha, x, rP) \subseteq QDepthCands(alpha, x, rC)
    <3> SUFFICES ASSUME NEW d \in QDepthCands(alpha, x, rP)
        PROVE d \in QDepthCands(alpha, x, rC)  OBVIOUS
    <3>1. PICK rc \in {y \in SBRefs(x, rP) : alpha \in DOMAIN y.maxqdepth} :
            d = QDepthCand(alpha, rc)
      BY DEF QDepthCands
    <3>2. PICK q \in SB : rc = MemoP(q)  BY <3>1, <1>sbP
    <3>3. alpha \in DOMAIN Memo(q).maxqdepth  BY <3>1, <3>2, <1>flds
    <3>4. Memo(q) \in {y \in SBRefs(x, rC) : alpha \in DOMAIN y.maxqdepth}
      BY <3>3, <1>sbC
    <3>5. QDepthCand(alpha, Memo(q)) = QDepthCand(alpha, MemoP(q))
      <4>1. alpha \in DOMAIN MemoP(q).maxqdepth  BY <3>1, <3>2
      <4> QED BY <4>1, <1>flds DEF QDepthCand
    <3> QED BY <3>1, <3>2, <3>4, <3>5 DEF QDepthCands
  <2>sup. QDepthCands(alpha, x, rC) \subseteq QDepthCands(alpha, x, rP)
    <3> SUFFICES ASSUME NEW d \in QDepthCands(alpha, x, rC)
        PROVE d \in QDepthCands(alpha, x, rP)  OBVIOUS
    <3>1. PICK rc \in {y \in SBRefs(x, rC) : alpha \in DOMAIN y.maxqdepth} :
            d = QDepthCand(alpha, rc)
      BY DEF QDepthCands
    <3>2. PICK q \in SB : rc = Memo(q)  BY <3>1, <1>sbC
    <3>3. alpha \in DOMAIN MemoP(q).maxqdepth  BY <3>1, <3>2, <1>flds
    <3>4. MemoP(q) \in {y \in SBRefs(x, rP) : alpha \in DOMAIN y.maxqdepth}
      BY <3>3, <1>sbP
    <3>5. QDepthCand(alpha, MemoP(q)) = QDepthCand(alpha, Memo(q))
      BY <3>3, <1>flds DEF QDepthCand
    <3> QED BY <3>1, <3>2, <3>4, <3>5 DEF QDepthCands
  <2> QED BY <2>sub, <2>sup
<1>front. \A alpha : RefFrontier(alpha, x, rP) = RefFrontier(alpha, x, rC)
  BY <1>qcands DEF RefFrontier
<1>pend. \A alpha : RefPending(alpha, x, rP) = RefPending(alpha, x, rC)
  <2> SUFFICES ASSUME NEW alpha
      PROVE RefPending(alpha, x, rP) = RefPending(alpha, x, rC)
    OBVIOUS
  <2>fr. RefFrontier(alpha, x, rP) = RefFrontier(alpha, x, rC)  BY <1>front
  <2>sub. RefPending(alpha, x, rP) \subseteq RefPending(alpha, x, rC)
    <3> SUFFICES ASSUME NEW z \in RefPending(alpha, x, rP)
        PROVE z \in RefPending(alpha, x, rC)  OBVIOUS
    <3>1. PICK rc \in {y \in SBRefs(x, rP) :
                         /\ alpha \in DOMAIN y.maxqdepth
                         /\ y.maxqdepth[alpha] = RefFrontier(alpha, x, rP)} :
            z \in RefPendingPart(alpha, rc)
      BY DEF RefPending
    <3>2. PICK q \in SB : rc = MemoP(q)  BY <3>1, <1>sbP
    <3>3. /\ alpha \in DOMAIN Memo(q).maxqdepth
          /\ Memo(q).maxqdepth[alpha] = RefFrontier(alpha, x, rC)
      BY <3>1, <3>2, <1>flds, <2>fr
    <3>4. Memo(q) \in {y \in SBRefs(x, rC) :
                         /\ alpha \in DOMAIN y.maxqdepth
                         /\ y.maxqdepth[alpha] = RefFrontier(alpha, x, rC)}
      BY <3>3, <1>sbC
    <3>5. RefPendingPart(alpha, Memo(q)) = RefPendingPart(alpha, MemoP(q))
      <4>1. alpha \in DOMAIN MemoP(q).maxqdepth  BY <3>1, <3>2
      <4> QED BY <4>1, <1>flds DEF RefPendingPart
    <3> QED BY <3>1, <3>2, <3>4, <3>5 DEF RefPending
  <2>sup. RefPending(alpha, x, rC) \subseteq RefPending(alpha, x, rP)
    <3> SUFFICES ASSUME NEW z \in RefPending(alpha, x, rC)
        PROVE z \in RefPending(alpha, x, rP)  OBVIOUS
    <3>1. PICK rc \in {y \in SBRefs(x, rC) :
                         /\ alpha \in DOMAIN y.maxqdepth
                         /\ y.maxqdepth[alpha] = RefFrontier(alpha, x, rC)} :
            z \in RefPendingPart(alpha, rc)
      BY DEF RefPending
    <3>2. PICK q \in SB : rc = Memo(q)  BY <3>1, <1>sbC
    <3>3. /\ alpha \in DOMAIN MemoP(q).maxqdepth
          /\ MemoP(q).maxqdepth[alpha] = RefFrontier(alpha, x, rP)
      BY <3>1, <3>2, <1>flds, <2>fr
    <3>4. MemoP(q) \in {y \in SBRefs(x, rP) :
                          /\ alpha \in DOMAIN y.maxqdepth
                          /\ y.maxqdepth[alpha] = RefFrontier(alpha, x, rP)}
      BY <3>3, <1>sbP
    <3>5. RefPendingPart(alpha, MemoP(q)) = RefPendingPart(alpha, Memo(q))
      BY <3>3, <1>flds DEF RefPendingPart
    <3> QED BY <3>1, <3>2, <3>4, <3>5 DEF RefPending
  <2> QED BY <2>sub, <2>sup
<1>bump. \A alpha : Bump(alpha, x, rP) <=> Bump(alpha, x, rC)
  BY <1>pend DEF Bump
\* ----------------------------------------------------- caught and highesttwoas
<1>caP. CaughtAssemble(rP) = Caught(x)
  BY <1>tok, <1>tt, <1>tf, <1>ta, MemoPCaughtStep
<1>caC. CaughtAssemble(rC) = Caught(x)
  BY <1>xm, <1>sand, <1>tok, <1>tt, <1>tf, <1>ta, CaughtCover
<1>caeq. CaughtAssemble(rP) = CaughtAssemble(rC)  BY <1>caP, <1>caC
<1>htP. /\ DOMAIN HighestTwoAsAssemble(rP)
             = {l \in Learners : \E y \in TranExclusive(x) : l \in Lrns(y)}
        /\ \A l \in DOMAIN HighestTwoAsAssemble(rP) :
             /\ \E y \in TranExclusive(x) :
                  l \in Lrns(y)
                  /\ B(y) = HighestTwoAsAssemble(rP)[l].bal
             /\ \A y \in TranExclusive(x) :
                  l \in Lrns(y) => B(y) <= HighestTwoAsAssemble(rP)[l].bal
  BY <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, MemoPHTStep
<1>htC. HighestTwoAsCorrect(x, HighestTwoAsAssemble(rC))
  BY <1>xm, <1>sand, HighestTwoAsCover
<1>htdomeq. DOMAIN HighestTwoAsAssemble(rP) = DOMAIN HighestTwoAsAssemble(rC)
  BY <1>htP, <1>htC DEF HighestTwoAsCorrect
<1>htbaleq. \A l \in DOMAIN HighestTwoAsAssemble(rP) :
              HighestTwoAsAssemble(rP)[l].bal
                = HighestTwoAsAssemble(rC)[l].bal
  <2> SUFFICES ASSUME NEW l \in DOMAIN HighestTwoAsAssemble(rP)
      PROVE HighestTwoAsAssemble(rP)[l].bal
              = HighestTwoAsAssemble(rC)[l].bal
    OBVIOUS
  <2>lC. l \in DOMAIN HighestTwoAsAssemble(rC)  BY <1>htdomeq
  <2>cf. /\ HighestTwoAsAssemble(rC)[l]
              = Memo(HighestTwoAsAssemble(rC)[l].id)
         /\ HighestTwoAsAssemble(rC)[l].id \in TranExclusive(x)
         /\ l \in Lrns(HighestTwoAsAssemble(rC)[l].id)
         /\ \A y \in TranExclusive(x) :
              l \in Lrns(y) => B(y) <= B(HighestTwoAsAssemble(rC)[l].id)
    BY <1>htC, <2>lC DEF HighestTwoAsCorrect
  <2>cid. HighestTwoAsAssemble(rC)[l].id \in Messages  BY <2>cf, <1>teM
  <2>cbal. HighestTwoAsAssemble(rC)[l].bal
             = B(HighestTwoAsAssemble(rC)[l].id)
    <3>1. MemoBal(HighestTwoAsAssemble(rC)[l].id)
            = B(HighestTwoAsAssemble(rC)[l].id)
      BY <2>cid, <1>tok, <1>tt, <1>tf, <1>ta, <1>anp, BalRec
    <3> QED BY <2>cf, <3>1 DEF MemoBal
  <2>pw. PICK y \in TranExclusive(x) :
           l \in Lrns(y) /\ B(y) = HighestTwoAsAssemble(rP)[l].bal
    BY <1>htP
  <2>le1. HighestTwoAsAssemble(rP)[l].bal
            <= B(HighestTwoAsAssemble(rC)[l].id)
    BY <2>pw, <2>cf
  <2>le2. B(HighestTwoAsAssemble(rC)[l].id)
            <= HighestTwoAsAssemble(rP)[l].bal
    BY <2>cf, <1>htP
  <2>nat1. HighestTwoAsAssemble(rP)[l].bal \in Nat
    <3>1. y \in Messages  BY <2>pw, <1>teM
    <3>2. B(y) \in Ballots  BY <3>1, <1>tok, <1>tf, <1>anp, BBallot
    <3> QED BY <2>pw, <3>2 DEF Ballots
  <2>nat2. B(HighestTwoAsAssemble(rC)[l].id) \in Nat
    <3>1. B(HighestTwoAsAssemble(rC)[l].id) \in Ballots
      BY <2>cid, <1>tok, <1>tf, <1>anp, BBallot
    <3> QED BY <3>1 DEF Ballots
  <2> QED BY <2>le1, <2>le2, <2>nat1, <2>nat2, <2>cbal, SMT
\* ------------------------------------------------------------ fresh, isoneb
<1>fresh. \A alpha : FreshAssemble(alpha, x, rP) <=> FreshAssemble(alpha, x, rC)
  <2> SUFFICES ASSUME NEW alpha
      PROVE FreshAssemble(alpha, x, rP) <=> FreshAssemble(alpha, x, rC)
    OBVIOUS
  <2>set. ConFromCaught(alpha, CaughtAssemble(rP))
            \cap DOMAIN HighestTwoAsAssemble(rP)
          = ConFromCaught(alpha, CaughtAssemble(rC))
            \cap DOMAIN HighestTwoAsAssemble(rC)
    BY <1>caeq, <1>htdomeq
  <2>f. FreshAssemble(alpha, x, rP) => FreshAssemble(alpha, x, rC)
    <3> SUFFICES ASSUME FreshAssemble(alpha, x, rP),
                        NEW l \in ConFromCaught(alpha, CaughtAssemble(rC))
                                    \cap DOMAIN HighestTwoAsAssemble(rC)
        PROVE \/ BalToVal(HighestTwoAsAssemble(rC)[l].bal)
                   = BalToVal(BalAssemble(x, rC))
              \/ \E l2 \in ConFromCaught(alpha, CaughtAssemble(rC))
                             \cap DOMAIN HighestTwoAsAssemble(rC) :
                   HighestTwoAsAssemble(rC)[l2].bal
                     > HighestTwoAsAssemble(rC)[l].bal
      BY DEF FreshAssemble
    <3>lP. l \in ConFromCaught(alpha, CaughtAssemble(rP))
                   \cap DOMAIN HighestTwoAsAssemble(rP)
      BY <2>set
    <3>1. \/ BalToVal(HighestTwoAsAssemble(rP)[l].bal)
               = BalToVal(BalAssemble(x, rP))
          \/ \E l2 \in ConFromCaught(alpha, CaughtAssemble(rP))
                         \cap DOMAIN HighestTwoAsAssemble(rP) :
               HighestTwoAsAssemble(rP)[l2].bal
                 > HighestTwoAsAssemble(rP)[l].bal
      BY <3>lP DEF FreshAssemble
    <3>lb. HighestTwoAsAssemble(rP)[l].bal = HighestTwoAsAssemble(rC)[l].bal
      BY <3>lP, <1>htbaleq
    <3>a. CASE BalToVal(HighestTwoAsAssemble(rP)[l].bal)
                 = BalToVal(BalAssemble(x, rP))
      <4> QED BY <3>a, <3>lb, <1>baleq
    <3>b. CASE \E l2 \in ConFromCaught(alpha, CaughtAssemble(rP))
                           \cap DOMAIN HighestTwoAsAssemble(rP) :
                 HighestTwoAsAssemble(rP)[l2].bal
                   > HighestTwoAsAssemble(rP)[l].bal
      <4>1. PICK l2 \in ConFromCaught(alpha, CaughtAssemble(rP))
                          \cap DOMAIN HighestTwoAsAssemble(rP) :
              HighestTwoAsAssemble(rP)[l2].bal
                > HighestTwoAsAssemble(rP)[l].bal
        BY <3>b
      <4>2. l2 \in ConFromCaught(alpha, CaughtAssemble(rC))
                     \cap DOMAIN HighestTwoAsAssemble(rC)
        BY <4>1, <2>set
      <4>3. HighestTwoAsAssemble(rP)[l2].bal
              = HighestTwoAsAssemble(rC)[l2].bal
        BY <4>1, <1>htbaleq
      <4> QED BY <4>1, <4>2, <4>3, <3>lb
    <3> QED BY <3>1, <3>a, <3>b
  <2>b. FreshAssemble(alpha, x, rC) => FreshAssemble(alpha, x, rP)
    <3> SUFFICES ASSUME FreshAssemble(alpha, x, rC),
                        NEW l \in ConFromCaught(alpha, CaughtAssemble(rP))
                                    \cap DOMAIN HighestTwoAsAssemble(rP)
        PROVE \/ BalToVal(HighestTwoAsAssemble(rP)[l].bal)
                   = BalToVal(BalAssemble(x, rP))
              \/ \E l2 \in ConFromCaught(alpha, CaughtAssemble(rP))
                             \cap DOMAIN HighestTwoAsAssemble(rP) :
                   HighestTwoAsAssemble(rP)[l2].bal
                     > HighestTwoAsAssemble(rP)[l].bal
      BY DEF FreshAssemble
    <3>lC. l \in ConFromCaught(alpha, CaughtAssemble(rC))
                   \cap DOMAIN HighestTwoAsAssemble(rC)
      BY <2>set
    <3>1. \/ BalToVal(HighestTwoAsAssemble(rC)[l].bal)
               = BalToVal(BalAssemble(x, rC))
          \/ \E l2 \in ConFromCaught(alpha, CaughtAssemble(rC))
                         \cap DOMAIN HighestTwoAsAssemble(rC) :
               HighestTwoAsAssemble(rC)[l2].bal
                 > HighestTwoAsAssemble(rC)[l].bal
      BY <3>lC DEF FreshAssemble
    <3>lb. HighestTwoAsAssemble(rP)[l].bal = HighestTwoAsAssemble(rC)[l].bal
      BY <1>htbaleq
    <3>a. CASE BalToVal(HighestTwoAsAssemble(rC)[l].bal)
                 = BalToVal(BalAssemble(x, rC))
      <4> QED BY <3>a, <3>lb, <1>baleq
    <3>b. CASE \E l2 \in ConFromCaught(alpha, CaughtAssemble(rC))
                           \cap DOMAIN HighestTwoAsAssemble(rC) :
                 HighestTwoAsAssemble(rC)[l2].bal
                   > HighestTwoAsAssemble(rC)[l].bal
      <4>1. PICK l2 \in ConFromCaught(alpha, CaughtAssemble(rC))
                          \cap DOMAIN HighestTwoAsAssemble(rC) :
              HighestTwoAsAssemble(rC)[l2].bal
                > HighestTwoAsAssemble(rC)[l].bal
        BY <3>b
      <4>2. l2 \in ConFromCaught(alpha, CaughtAssemble(rP))
                     \cap DOMAIN HighestTwoAsAssemble(rP)
        BY <4>1, <2>set
      <4>3. HighestTwoAsAssemble(rP)[l2].bal
              = HighestTwoAsAssemble(rC)[l2].bal
        BY <4>2, <1>htbaleq
      <4> QED BY <4>1, <4>2, <4>3, <3>lb
    <3> QED BY <3>1, <3>a, <3>b
  <2> QED BY <2>f, <2>b
<1>oneb. IsOneBAssemble(x, rP) <=> IsOneBAssemble(x, rC)
  <2>f. IsOneBAssemble(x, rP) => IsOneBAssemble(x, rC)
    <3> SUFFICES ASSUME IsOneBAssemble(x, rP)
        PROVE IsOneBAssemble(x, rC)  OBVIOUS
    <3>np. ~IsProposal(x)  BY DEF IsOneBAssemble
    <3>1. PICK rc \in rP :
            /\ IsProposal(rc.id)
            /\ rc.bal = BalAssemble(x, rP)
            /\ rc.newbal
            /\ \A rc2 \in rP : rc2 = rc \/ rc2.bal < BalAssemble(x, rP)
      BY DEF IsOneBAssemble
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3>3. /\ IsProposal(Memo(q).id)
          /\ Memo(q).bal = BalAssemble(x, rC)
          /\ Memo(q).newbal
      BY <3>1, <3>2, <1>flds, <1>baleq
    <3>4. \A rc2 \in rC : rc2 = Memo(q) \/ rc2.bal < BalAssemble(x, rC)
      <4> SUFFICES ASSUME NEW rc2 \in rC
          PROVE rc2 = Memo(q) \/ rc2.bal < BalAssemble(x, rC)  OBVIOUS
      <4>1. PICK q2 \in pr : rc2 = Memo(q2)  OBVIOUS
      <4>2. MemoP(q2) = MemoP(q) \/ MemoP(q2).bal < BalAssemble(x, rP)
        BY <3>1, <3>2
      <4>a. CASE MemoP(q2) = MemoP(q)
        <5>1. MemoP(q2).id = q2 /\ MemoP(q).id = q
          BY <1>ihq DEF MemoPGood
        <5>2. q2 = q  BY <4>a, <5>1
        <5> QED BY <4>1, <5>2
      <4>b. CASE MemoP(q2).bal < BalAssemble(x, rP)
        <5>1. Memo(q2).bal < BalAssemble(x, rC)
          BY <4>b, <1>flds, <1>baleq
        <5> QED BY <4>1, <5>1
      <4> QED BY <4>2, <4>a, <4>b
    <3>5. Memo(q) \in rC  OBVIOUS
    <3> QED BY <3>np, <3>3, <3>4, <3>5 DEF IsOneBAssemble
  <2>b. IsOneBAssemble(x, rC) => IsOneBAssemble(x, rP)
    <3> SUFFICES ASSUME IsOneBAssemble(x, rC)
        PROVE IsOneBAssemble(x, rP)  OBVIOUS
    <3>np. ~IsProposal(x)  BY DEF IsOneBAssemble
    <3>1. PICK rc \in rC :
            /\ IsProposal(rc.id)
            /\ rc.bal = BalAssemble(x, rC)
            /\ rc.newbal
            /\ \A rc2 \in rC : rc2 = rc \/ rc2.bal < BalAssemble(x, rC)
      BY DEF IsOneBAssemble
    <3>2. PICK q \in pr : rc = Memo(q)  BY <3>1
    <3>3. /\ IsProposal(MemoP(q).id)
          /\ MemoP(q).bal = BalAssemble(x, rP)
          /\ MemoP(q).newbal
      BY <3>1, <3>2, <1>flds, <1>baleq
    <3>4. \A rc2 \in rP : rc2 = MemoP(q) \/ rc2.bal < BalAssemble(x, rP)
      <4> SUFFICES ASSUME NEW rc2 \in rP
          PROVE rc2 = MemoP(q) \/ rc2.bal < BalAssemble(x, rP)  OBVIOUS
      <4>1. PICK q2 \in pr : rc2 = MemoP(q2)  OBVIOUS
      <4>2. Memo(q2) = Memo(q) \/ Memo(q2).bal < BalAssemble(x, rC)
        BY <3>1, <3>2
      <4>a. CASE Memo(q2) = Memo(q)
        <5>1. Memo(q2).id = q2 /\ Memo(q).id = q  BY <1>midp
        <5>2. q2 = q  BY <4>a, <5>1
        <5> QED BY <4>1, <5>2
      <4>b. CASE Memo(q2).bal < BalAssemble(x, rC)
        <5>1. MemoP(q2).bal < BalAssemble(x, rP)
          BY <4>b, <1>flds, <1>baleq
        <5> QED BY <4>1, <5>1
      <4> QED BY <4>2, <4>a, <4>b
    <3>5. MemoP(q) \in rP  OBVIOUS
    <3> QED BY <3>np, <3>3, <3>4, <3>5 DEF IsOneBAssemble
  <2> QED BY <2>f, <2>b
\* ------------------------------------------------------- x's own attestation
<1>self0. \A alpha : SelfL0(alpha, x, rP) <=> SelfL0(alpha, x, rC)
  BY <1>oneb, <1>fresh DEF SelfL0
<1>selfF. \A alpha : SelfAtFrontier(alpha, x, rP)
                       <=> SelfAtFrontier(alpha, x, rC)
  BY <1>front, <1>self0 DEF SelfAtFrontier
<1>mqdom. MQDomain(x, rP) = MQDomain(x, rC)
  BY <1>qdom, <1>self0 DEF MQDomain
\* ----------------------------------------------------------------- assemblies
<1>mqeq. MaxQDepthAssemble(x, rP) = MaxQDepthAssemble(x, rC)
  BY <1>mqdom, <1>qdom, <1>bump, <1>front DEF MaxQDepthAssemble
<1>pqeq. PendingQdAssemble(x, rP) = PendingQdAssemble(x, rC)
  BY <1>mqdom, <1>qdom, <1>bump, <1>pend, <1>selfF DEF PendingQdAssemble
<1>lreq. LrnsAssemble(x, rP) = LrnsAssemble(x, rC)
  BY <1>qdom, <1>front, <1>bump DEF LrnsAssemble
<1>lrC. LrnsAssemble(x, rC) = Lrns(x)
  BY <1>xm, <1>sand, LrnsCover
<1>mqC. MaxQDepthCorrect(x, MaxQDepthAssemble(x, rC), PendingQdAssemble(x, rC))
  BY <1>xm, <1>sand, MaxQDepthCover
<1> QED BY <1>lreq, <1>lrC, <1>mqeq, <1>pqeq, <1>mqC
=============================================================================
