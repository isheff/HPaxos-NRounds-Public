--------------------- MODULE DecideableProposalPExists ---------------------
EXTENDS MessageInterface,
        BetaStarExists, TopLearnerMsgCorrect, TranClosureClosed,
        BBallot, PExists

LEMMA DecideableProposalPExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         \A x \in TranClosure(m) : B(x) < bal
  PROVE \E p \in Proposals :
          /\ TranExclusive(p) = DecideableProposalTranExclusive(m)
          /\ B(p) > bal
          /\ Sig(p) \notin Acceptors
          /\ V(p) = DecideableProposalV(alpha, bal, m)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>via. AlwaysAValue  BY DEF ValueInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1> DEFINE S == ConFromCaught(alpha, CaughtS(TranClosure(m)))
<1> DEFINE SS == S \cap RelevantLearners(m)
<1>sL. S \subseteq Learners  BY DEF ConFromCaught
<1>caseNE. CASE SS # {}
  <2>ssL. SS \in SUBSET Learners
    <3>1. RelevantLearners(m) \subseteq Learners  BY DEF RelevantLearners
    <3> QED BY <3>1
  <2>ssrel. \A beta \in SS : \E x \in TranClosure(m) : beta \in Lrns(x)
    <3> SUFFICES ASSUME NEW beta \in SS PROVE \E x \in TranClosure(m) : beta \in Lrns(x)  OBVIOUS
    <3>1. beta \in RelevantLearners(m)  OBVIOUS
    <3> QED BY <3>1 DEF RelevantLearners
  <2>bse. \E beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
    BY <2>ssL, <1>caseNE, <2>ssrel, <1>balnat, <1>bound, BetaStarExists
  <2> DEFINE betastar == CHOOSE beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
  <2>bsprop. betastar \in SS /\ (\A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,betastar))
    BY <2>bse
  <2>bsS. betastar \in S  BY <2>bsprop
  <2>bsRel. betastar \in RelevantLearners(m)  BY <2>bsprop
  <2>bsLrns. betastar \in Lrns(TopLearnerMsg(m,betastar))
    <3>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <2>bsRel DEF RelevantLearners
    <3> QED BY <3>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
  <2>xbmsgs. TopLearnerMsg(m,betastar) \in TranClosure(m)
    <3>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <2>bsRel DEF RelevantLearners
    <3> QED BY <3>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
  <2>xbm. TopLearnerMsg(m,betastar) \in Messages  BY <2>xbmsgs, <1>mi, TranClosureClosed
  <2>vval. V(TopLearnerMsg(m,betastar)) \in Values
    <3>1. B(TopLearnerMsg(m,betastar)) \in Ballots  BY <2>xbm, <1>mi, BBallot
    <3> QED BY <3>1, <1>via DEF V, AlwaysAValue
  <2>dpv. DecideableProposalV(alpha,bal,m) = V(TopLearnerMsg(m,betastar))
    BY <1>caseNE DEF DecideableProposalV
  <2>pex. \E p \in Proposals :
            /\ TranExclusive(p) = TranClosure(CQ(m))
            /\ B(p) > bal
            /\ Sig(p) \notin Acceptors
            /\ V(p) = V(TopLearnerMsg(m,betastar))
    BY <1>mi, LearnerGraphAssumptions, ValueInterfaceAssumptions, <2>vval, PExists
  <2> QED BY <2>pex, <2>dpv DEF DecideableProposalTranExclusive
<1>caseE. CASE SS = {}
  <2>vval. BalToVal(bal) \in Values  BY <1>via DEF AlwaysAValue
  <2>dpv. DecideableProposalV(alpha,bal,m) = BalToVal(bal)  BY <1>caseE DEF DecideableProposalV
  <2>pex. \E p \in Proposals :
            /\ TranExclusive(p) = TranClosure(CQ(m))
            /\ B(p) > bal
            /\ Sig(p) \notin Acceptors
            /\ V(p) = BalToVal(bal)
    BY <1>mi, LearnerGraphAssumptions, ValueInterfaceAssumptions, <2>vval, PExists
  <2> QED BY <2>pex, <2>dpv DEF DecideableProposalTranExclusive
<1> QED BY <1>caseNE, <1>caseE
====================================================================
