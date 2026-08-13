------------------------------- MODULE WFRAgree -------------------------------
\* The candidate check does not care which memo the priors are stored as:
\* over a prior set of real messages, the WFR operators read exactly the
\* value-determined member fields (id, bal, newbal, and the frontier maps at
\* a learner), so their values over the priors' MemoP records coincide with
\* their values over the canonical Memos.
\*
\* This is the candidate-level counterpart of MemoPLrnsMQStep's transfer,
\* and it is what lets WellFormedRec be defined over MemoP -- what an
\* implementation actually stores -- while CWellFormedRec keeps citing the
\* canonical-memo machinery (BalU / IsOneBU / LrnsU).  The caught conjunct
\* is NOT here: its assembly reads the deepestknown entries, which the two
\* memos may CHOOSE differently; it is handled semantically instead, by
\* MemoPCaughtCand.
EXTENDS WellFormedRecDef, MemoPDefs, MemoPFields, MemoPGoodInv, MemoRec,
        CFields
LOCAL INSTANCE TLAPS

LEMMA WFRAgree ==
  ASSUME MessageInterfaceAssumptions,
         LearnersMightAgree, ValidLearnerGraphAssumption,
         MessageInterface = CMI,
         NEW sdr, NEW pl,
         NEW pr, pr \subseteq CMessages
  PROVE /\ WFRBal(pl, {MemoP(p) : p \in pr})
             = WFRBal(pl, {Memo(p) : p \in pr})
        /\ (WFRIsOneB(pl, {MemoP(p) : p \in pr})
              <=> WFRIsOneB(pl, {Memo(p) : p \in pr}))
        /\ WFRLrns(sdr, pl, {MemoP(p) : p \in pr})
             = WFRLrns(sdr, pl, {Memo(p) : p \in pr})
        /\ (WFRIsTwoA(sdr, pl, {MemoP(p) : p \in pr})
              <=> WFRIsTwoA(sdr, pl, {Memo(p) : p \in pr}))
<1> DEFINE rP == {MemoP(q) : q \in pr}
<1> DEFINE rC == {Memo(q) : q \in pr}
\* ------------------------------------------------------------------ prelude
<1>tok. TypeOKMessageInterface  BY DEF MessageInterfaceAssumptions
<1>tf. TranFinite  BY DEF MessageInterfaceAssumptions
<1>tt. TranTrans  BY DEF MessageInterfaceAssumptions
<1>ta. TranAcyclic  BY DEF MessageInterfaceAssumptions
<1>anp. AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>prMsg. pr \subseteq Messages  BY CFields
<1>ihq. \A q \in pr : MemoPGood(q)  BY MemoPGoodInv
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
\* ---------------------------------------------------------------------- bal
<1>balimg. {rc.bal : rc \in rP} = {rc.bal : rc \in rC}
  <2>sub. {rc.bal : rc \in rP} \subseteq {rc.bal : rc \in rC}
    <3> SUFFICES ASSUME NEW rc \in rP
        PROVE rc.bal \in {rc2.bal : rc2 \in rC}  OBVIOUS
    <3>1. PICK q \in pr : rc = MemoP(q)  OBVIOUS
    <3>2. Memo(q) \in rC  OBVIOUS
    <3> QED BY <3>1, <3>2, <1>flds
  <2>sup. {rc.bal : rc \in rC} \subseteq {rc.bal : rc \in rP}
    <3> SUFFICES ASSUME NEW rc \in rC
        PROVE rc.bal \in {rc2.bal : rc2 \in rP}  OBVIOUS
    <3>1. PICK q \in pr : rc = Memo(q)  OBVIOUS
    <3>2. MemoP(q) \in rP  OBVIOUS
    <3> QED BY <3>1, <3>2, <1>flds
  <2> QED BY <2>sub, <2>sup
<1>bal. WFRBal(pl, rP) = WFRBal(pl, rC)
  BY <1>balimg DEF WFRBal
\* -------------------------------------------------------- same-ballot priors
<1> DEFINE SB == {q \in pr : Memo(q).bal = WFRBal(pl, rC)}
<1>sbP. WFRSBRefs(pl, rP) = {MemoP(q) : q \in SB}
  <2>sub. WFRSBRefs(pl, rP) \subseteq {MemoP(q) : q \in SB}
    <3> SUFFICES ASSUME NEW rc \in WFRSBRefs(pl, rP)
        PROVE rc \in {MemoP(q) : q \in SB}  OBVIOUS
    <3>1. rc \in rP /\ rc.bal = WFRBal(pl, rP)  BY DEF WFRSBRefs
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3>3. Memo(q).bal = WFRBal(pl, rC)  BY <3>1, <3>2, <1>flds, <1>bal
    <3> QED BY <3>2, <3>3
  <2>sup. {MemoP(q) : q \in SB} \subseteq WFRSBRefs(pl, rP)
    <3> SUFFICES ASSUME NEW q \in SB
        PROVE MemoP(q) \in WFRSBRefs(pl, rP)  OBVIOUS
    <3>1. MemoP(q) \in rP  OBVIOUS
    <3>2. MemoP(q).bal = WFRBal(pl, rP)  BY <1>flds, <1>bal
    <3> QED BY <3>1, <3>2 DEF WFRSBRefs
  <2> QED BY <2>sub, <2>sup
<1>sbC. WFRSBRefs(pl, rC) = {Memo(q) : q \in SB}
  <2>sub. WFRSBRefs(pl, rC) \subseteq {Memo(q) : q \in SB}
    <3> SUFFICES ASSUME NEW rc \in WFRSBRefs(pl, rC)
        PROVE rc \in {Memo(q) : q \in SB}  OBVIOUS
    <3>1. rc \in rC /\ rc.bal = WFRBal(pl, rC)  BY DEF WFRSBRefs
    <3>2. PICK q \in pr : rc = Memo(q)  BY <3>1
    <3> QED BY <3>1, <3>2
  <2>sup. {Memo(q) : q \in SB} \subseteq WFRSBRefs(pl, rC)
    <3> SUFFICES ASSUME NEW q \in SB
        PROVE Memo(q) \in WFRSBRefs(pl, rC)  OBVIOUS
    <3>1. Memo(q) \in rC  OBVIOUS
    <3> QED BY <3>1 DEF WFRSBRefs
  <2> QED BY <2>sub, <2>sup
\* -------------------------------------------------------- frontier operators
<1>qdom. WFRQDom(pl, rP) = WFRQDom(pl, rC)
  <2>sub. WFRQDom(pl, rP) \subseteq WFRQDom(pl, rC)
    <3> SUFFICES ASSUME NEW alpha \in WFRQDom(pl, rP)
        PROVE alpha \in WFRQDom(pl, rC)  OBVIOUS
    <3>1. alpha \in Learners  BY DEF WFRQDom
    <3>2. PICK rc \in WFRSBRefs(pl, rP) : alpha \in DOMAIN rc.maxqdepth
      BY DEF WFRQDom
    <3>3. PICK q \in SB : rc = MemoP(q)  BY <3>2, <1>sbP
    <3>4. alpha \in DOMAIN Memo(q).maxqdepth  BY <3>2, <3>3, <1>flds
    <3>5. Memo(q) \in WFRSBRefs(pl, rC)  BY <1>sbC
    <3> QED BY <3>1, <3>4, <3>5 DEF WFRQDom
  <2>sup. WFRQDom(pl, rC) \subseteq WFRQDom(pl, rP)
    <3> SUFFICES ASSUME NEW alpha \in WFRQDom(pl, rC)
        PROVE alpha \in WFRQDom(pl, rP)  OBVIOUS
    <3>1. alpha \in Learners  BY DEF WFRQDom
    <3>2. PICK rc \in WFRSBRefs(pl, rC) : alpha \in DOMAIN rc.maxqdepth
      BY DEF WFRQDom
    <3>3. PICK q \in SB : rc = Memo(q)  BY <3>2, <1>sbC
    <3>4. alpha \in DOMAIN MemoP(q).maxqdepth  BY <3>2, <3>3, <1>flds
    <3>5. MemoP(q) \in WFRSBRefs(pl, rP)  BY <1>sbP
    <3> QED BY <3>1, <3>4, <3>5 DEF WFRQDom
  <2> QED BY <2>sub, <2>sup
<1>qcands. \A alpha : WFRQDepthCands(alpha, pl, rP)
                        = WFRQDepthCands(alpha, pl, rC)
  <2> SUFFICES ASSUME NEW alpha
      PROVE WFRQDepthCands(alpha, pl, rP) = WFRQDepthCands(alpha, pl, rC)
    OBVIOUS
  <2>sub. WFRQDepthCands(alpha, pl, rP) \subseteq WFRQDepthCands(alpha, pl, rC)
    <3> SUFFICES ASSUME NEW d \in WFRQDepthCands(alpha, pl, rP)
        PROVE d \in WFRQDepthCands(alpha, pl, rC)  OBVIOUS
    <3>1. PICK rc \in {y \in WFRSBRefs(pl, rP) :
                         alpha \in DOMAIN y.maxqdepth} :
            d = QDepthCand(alpha, rc)
      BY DEF WFRQDepthCands
    <3>2. PICK q \in SB : rc = MemoP(q)  BY <3>1, <1>sbP
    <3>3. alpha \in DOMAIN Memo(q).maxqdepth  BY <3>1, <3>2, <1>flds
    <3>4. Memo(q) \in {y \in WFRSBRefs(pl, rC) :
                         alpha \in DOMAIN y.maxqdepth}
      BY <3>3, <1>sbC
    <3>5. QDepthCand(alpha, Memo(q)) = QDepthCand(alpha, MemoP(q))
      <4>1. alpha \in DOMAIN MemoP(q).maxqdepth  BY <3>1, <3>2
      <4> QED BY <4>1, <1>flds DEF QDepthCand
    <3> QED BY <3>1, <3>2, <3>4, <3>5 DEF WFRQDepthCands
  <2>sup. WFRQDepthCands(alpha, pl, rC) \subseteq WFRQDepthCands(alpha, pl, rP)
    <3> SUFFICES ASSUME NEW d \in WFRQDepthCands(alpha, pl, rC)
        PROVE d \in WFRQDepthCands(alpha, pl, rP)  OBVIOUS
    <3>1. PICK rc \in {y \in WFRSBRefs(pl, rC) :
                         alpha \in DOMAIN y.maxqdepth} :
            d = QDepthCand(alpha, rc)
      BY DEF WFRQDepthCands
    <3>2. PICK q \in SB : rc = Memo(q)  BY <3>1, <1>sbC
    <3>3. alpha \in DOMAIN MemoP(q).maxqdepth  BY <3>1, <3>2, <1>flds
    <3>4. MemoP(q) \in {y \in WFRSBRefs(pl, rP) :
                          alpha \in DOMAIN y.maxqdepth}
      BY <3>3, <1>sbP
    <3>5. QDepthCand(alpha, MemoP(q)) = QDepthCand(alpha, Memo(q))
      BY <3>3, <1>flds DEF QDepthCand
    <3> QED BY <3>1, <3>2, <3>4, <3>5 DEF WFRQDepthCands
  <2> QED BY <2>sub, <2>sup
<1>front. \A alpha : WFRRefFrontier(alpha, pl, rP)
                       = WFRRefFrontier(alpha, pl, rC)
  BY <1>qcands DEF WFRRefFrontier
<1>pend. \A alpha : WFRRefPending(alpha, pl, rP)
                      = WFRRefPending(alpha, pl, rC)
  <2> SUFFICES ASSUME NEW alpha
      PROVE WFRRefPending(alpha, pl, rP) = WFRRefPending(alpha, pl, rC)
    OBVIOUS
  <2>fr. WFRRefFrontier(alpha, pl, rP) = WFRRefFrontier(alpha, pl, rC)
    BY <1>front
  <2>sub. WFRRefPending(alpha, pl, rP) \subseteq WFRRefPending(alpha, pl, rC)
    <3> SUFFICES ASSUME NEW z \in WFRRefPending(alpha, pl, rP)
        PROVE z \in WFRRefPending(alpha, pl, rC)  OBVIOUS
    <3>1. PICK rc \in {y \in WFRSBRefs(pl, rP) :
                         /\ alpha \in DOMAIN y.maxqdepth
                         /\ y.maxqdepth[alpha]
                              = WFRRefFrontier(alpha, pl, rP)} :
            z \in RefPendingPart(alpha, rc)
      BY DEF WFRRefPending
    <3>2. PICK q \in SB : rc = MemoP(q)  BY <3>1, <1>sbP
    <3>3. /\ alpha \in DOMAIN Memo(q).maxqdepth
          /\ Memo(q).maxqdepth[alpha] = WFRRefFrontier(alpha, pl, rC)
      BY <3>1, <3>2, <1>flds, <2>fr
    <3>4. Memo(q) \in {y \in WFRSBRefs(pl, rC) :
                         /\ alpha \in DOMAIN y.maxqdepth
                         /\ y.maxqdepth[alpha]
                              = WFRRefFrontier(alpha, pl, rC)}
      BY <3>3, <1>sbC
    <3>5. RefPendingPart(alpha, Memo(q)) = RefPendingPart(alpha, MemoP(q))
      <4>1. alpha \in DOMAIN MemoP(q).maxqdepth  BY <3>1, <3>2
      <4> QED BY <4>1, <1>flds DEF RefPendingPart
    <3> QED BY <3>1, <3>2, <3>4, <3>5 DEF WFRRefPending
  <2>sup. WFRRefPending(alpha, pl, rC) \subseteq WFRRefPending(alpha, pl, rP)
    <3> SUFFICES ASSUME NEW z \in WFRRefPending(alpha, pl, rC)
        PROVE z \in WFRRefPending(alpha, pl, rP)  OBVIOUS
    <3>1. PICK rc \in {y \in WFRSBRefs(pl, rC) :
                         /\ alpha \in DOMAIN y.maxqdepth
                         /\ y.maxqdepth[alpha]
                              = WFRRefFrontier(alpha, pl, rC)} :
            z \in RefPendingPart(alpha, rc)
      BY DEF WFRRefPending
    <3>2. PICK q \in SB : rc = Memo(q)  BY <3>1, <1>sbC
    <3>3. /\ alpha \in DOMAIN MemoP(q).maxqdepth
          /\ MemoP(q).maxqdepth[alpha] = WFRRefFrontier(alpha, pl, rP)
      BY <3>1, <3>2, <1>flds, <2>fr
    <3>4. MemoP(q) \in {y \in WFRSBRefs(pl, rP) :
                          /\ alpha \in DOMAIN y.maxqdepth
                          /\ y.maxqdepth[alpha]
                               = WFRRefFrontier(alpha, pl, rP)}
      BY <3>3, <1>sbP
    <3>5. RefPendingPart(alpha, MemoP(q)) = RefPendingPart(alpha, Memo(q))
      BY <3>3, <1>flds DEF RefPendingPart
    <3> QED BY <3>1, <3>2, <3>4, <3>5 DEF WFRRefPending
  <2> QED BY <2>sub, <2>sup
<1>bump. \A alpha : WFRBump(alpha, sdr, pl, rP) <=> WFRBump(alpha, sdr, pl, rC)
  BY <1>pend DEF WFRBump
\* -------------------------------------------------------------------- lrns
<1>lrns. WFRLrns(sdr, pl, rP) = WFRLrns(sdr, pl, rC)
  BY <1>qdom, <1>front, <1>bump DEF WFRLrns
<1>twoa. WFRIsTwoA(sdr, pl, rP) <=> WFRIsTwoA(sdr, pl, rC)
  BY <1>lrns DEF WFRIsTwoA
\* ------------------------------------------------------------------- isoneb
<1>oneb. WFRIsOneB(pl, rP) <=> WFRIsOneB(pl, rC)
  <2>f. WFRIsOneB(pl, rP) => WFRIsOneB(pl, rC)
    <3> SUFFICES ASSUME WFRIsOneB(pl, rP) PROVE WFRIsOneB(pl, rC)  OBVIOUS
    <3>np. pl \notin CProposal  BY DEF WFRIsOneB
    <3>1. PICK rc \in rP :
            /\ CIsProposal(rc.id)
            /\ rc.bal = WFRBal(pl, rP)
            /\ rc.newbal
            /\ \A rc2 \in rP : rc2 = rc \/ rc2.bal < WFRBal(pl, rP)
      BY DEF WFRIsOneB
    <3>2. PICK q \in pr : rc = MemoP(q)  BY <3>1
    <3>3. /\ CIsProposal(Memo(q).id)
          /\ Memo(q).bal = WFRBal(pl, rC)
          /\ Memo(q).newbal
      BY <3>1, <3>2, <1>flds, <1>bal
    <3>4. \A rc2 \in rC : rc2 = Memo(q) \/ rc2.bal < WFRBal(pl, rC)
      <4> SUFFICES ASSUME NEW rc2 \in rC
          PROVE rc2 = Memo(q) \/ rc2.bal < WFRBal(pl, rC)  OBVIOUS
      <4>1. PICK q2 \in pr : rc2 = Memo(q2)  OBVIOUS
      <4>2. MemoP(q2) = MemoP(q) \/ MemoP(q2).bal < WFRBal(pl, rP)
        BY <3>1, <3>2
      <4>a. CASE MemoP(q2) = MemoP(q)
        <5>1. MemoP(q2).id = q2 /\ MemoP(q).id = q
          BY <1>ihq DEF MemoPGood
        <5>2. q2 = q  BY <4>a, <5>1
        <5> QED BY <4>1, <5>2
      <4>b. CASE MemoP(q2).bal < WFRBal(pl, rP)
        <5>1. Memo(q2).bal < WFRBal(pl, rC)  BY <4>b, <1>flds, <1>bal
        <5> QED BY <4>1, <5>1
      <4> QED BY <4>2, <4>a, <4>b
    <3>5. Memo(q) \in rC  OBVIOUS
    <3> QED BY <3>np, <3>3, <3>4, <3>5 DEF WFRIsOneB
  <2>b. WFRIsOneB(pl, rC) => WFRIsOneB(pl, rP)
    <3> SUFFICES ASSUME WFRIsOneB(pl, rC) PROVE WFRIsOneB(pl, rP)  OBVIOUS
    <3>np. pl \notin CProposal  BY DEF WFRIsOneB
    <3>1. PICK rc \in rC :
            /\ CIsProposal(rc.id)
            /\ rc.bal = WFRBal(pl, rC)
            /\ rc.newbal
            /\ \A rc2 \in rC : rc2 = rc \/ rc2.bal < WFRBal(pl, rC)
      BY DEF WFRIsOneB
    <3>2. PICK q \in pr : rc = Memo(q)  BY <3>1
    <3>3. /\ CIsProposal(MemoP(q).id)
          /\ MemoP(q).bal = WFRBal(pl, rP)
          /\ MemoP(q).newbal
      BY <3>1, <3>2, <1>flds, <1>bal
    <3>4. \A rc2 \in rP : rc2 = MemoP(q) \/ rc2.bal < WFRBal(pl, rP)
      <4> SUFFICES ASSUME NEW rc2 \in rP
          PROVE rc2 = MemoP(q) \/ rc2.bal < WFRBal(pl, rP)  OBVIOUS
      <4>1. PICK q2 \in pr : rc2 = MemoP(q2)  OBVIOUS
      <4>2. Memo(q2) = Memo(q) \/ Memo(q2).bal < WFRBal(pl, rC)
        BY <3>1, <3>2
      <4>a. CASE Memo(q2) = Memo(q)
        <5>1. Memo(q2).id = q2 /\ Memo(q).id = q  BY <1>midp
        <5>2. q2 = q  BY <4>a, <5>1
        <5> QED BY <4>1, <5>2
      <4>b. CASE Memo(q2).bal < WFRBal(pl, rC)
        <5>1. MemoP(q2).bal < WFRBal(pl, rP)  BY <4>b, <1>flds, <1>bal
        <5> QED BY <4>1, <5>1
      <4> QED BY <4>2, <4>a, <4>b
    <3>5. MemoP(q) \in rP  OBVIOUS
    <3> QED BY <3>np, <3>3, <3>4, <3>5 DEF WFRIsOneB
  <2> QED BY <2>f, <2>b
<1> QED BY <1>bal, <1>oneb, <1>lrns, <1>twoa
=============================================================================
