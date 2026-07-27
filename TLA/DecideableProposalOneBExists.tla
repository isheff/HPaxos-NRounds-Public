------------------- MODULE DecideableProposalOneBExists -------------------
EXTENDS MessageInterface,
        CQSubTC, TranClosureClosed, TranClosureAbsorb, BBallot,
        BetaStarExists, TopLearnerMsgCorrect,
        OneBFresh, OneBFreshDegenerate

LEMMA DecideableProposalOneBExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         \A x \in TranClosure(m) : B(x) < bal,
         NEW p \in Proposals,
         TranExclusive(p) = DecideableProposalTranExclusive(m),
         B(p) > bal,
         Sig(p) \notin Acceptors,
         V(p) = DecideableProposalV(alpha, bal, m)
  PROVE \A a \in Acceptors :
          \A known \in SUBSET TranClosure(m) :
          (/\ IsFiniteSet(known)
           /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
          ) =>
            \E oneb \in Messages :
            (/\ Sig(oneb) = a
             /\ a \notin Caught(oneb)
             /\ IsOneB(oneb)
             /\ TranExclusive(oneb) = TranClosure(known \cup {p})
             /\ Fresh(alpha, oneb)
            )
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1> DEFINE S == ConFromCaught(alpha, CaughtS(TranClosure(m)))
<1> DEFINE SS == S \cap RelevantLearners(m)
<1>sL. S \subseteq Learners  BY DEF ConFromCaught
<1>tep. TranExclusive(p) = TranClosure(CQ(m))  BY DEF DecideableProposalTranExclusive
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, CQSubTC
<1>tesub. TranExclusive(p) \subseteq TranClosure(m)  BY <1>tep, <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
<1> DEFINE btarg == B(p)
<1>baltarg. bal < btarg  OBVIOUS
<1>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>btbal. btarg \in Ballots  BY <1>pmsg, <1>mi, BBallot
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
  <2>bsSraw. betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <2>bsS
  <2>bsRel. betastar \in RelevantLearners(m)  BY <2>bsprop
  <2>bstL. betastar \in Learners  BY <2>ssL, <2>bsprop
  <2>bsLrns. betastar \in Lrns(TopLearnerMsg(m,betastar))
    <3>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <2>bsRel DEF RelevantLearners
    <3> QED BY <3>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
  <2>bsMax. \A beta \in S : (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
    <3> SUFFICES ASSUME NEW beta \in S, \E x \in TranClosure(m) : beta \in Lrns(x)
                 PROVE BXBeta(m,beta) <= BXBeta(m,betastar)
      OBVIOUS
    <3>1. beta \in RelevantLearners(m)  BY <1>sL DEF RelevantLearners
    <3>2. beta \in SS  BY <3>1
    <3> QED BY <3>2, <2>bsprop
  <2>bsMaxraw. \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                 (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
    BY <2>bsMax
  <2>xbmsgs. TopLearnerMsg(m,betastar) \in TranClosure(m)
    <3>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <2>bsRel DEF RelevantLearners
    <3> QED BY <3>ex, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
  <2>dpv. DecideableProposalV(alpha,bal,m) = V(TopLearnerMsg(m,betastar))
    BY <1>caseNE DEF DecideableProposalV
  <2>vp. V(p) = V(TopLearnerMsg(m,betastar))  BY <2>dpv
  <2>exhyp. \E bal2 \in Ballots, btarg2 \in Ballots, betastar2 \in Learners :
              /\ TranExclusive(p) = TranClosure(CQ(m))
              /\ B(p) = btarg2
              /\ Sig(p) \notin Acceptors
              /\ (\A x \in TranClosure(m) : B(x) < bal2)
              /\ bal2 < btarg2
              /\ betastar2 \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
              /\ TopLearnerMsg(m,betastar2) \in TranClosure(m)
              /\ betastar2 \in Lrns(TopLearnerMsg(m,betastar2))
              /\ (\A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                   (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar2))
              /\ V(p) = V(TopLearnerMsg(m,betastar2))
    <3> WITNESS bal \in Ballots, btarg \in Ballots, betastar \in Learners
    <3> QED BY <1>tep, <1>bound, <1>baltarg, <2>bsSraw, <2>xbmsgs, <2>bsLrns, <2>bsMaxraw, <2>vp
  <2> QED BY MessageInterfaceAssumptions, LearnerGraphAssumptions, <2>exhyp, OneBFresh
<1>caseE. CASE SS = {}
  <2>capempty. S \cap RelevantLearners(m) = {}  BY <1>caseE
  <2>capemptyraw. ConFromCaught(alpha, CaughtS(TranClosure(m))) \cap RelevantLearners(m) = {}
    BY <2>capempty
  <2>exhyp. \E bal2 \in Ballots, btarg2 \in Ballots :
              /\ TranExclusive(p) = TranClosure(CQ(m))
              /\ B(p) = btarg2
              /\ Sig(p) \notin Acceptors
              /\ (\A x \in TranClosure(m) : B(x) < bal2)
              /\ bal2 < btarg2
    <3> WITNESS bal \in Ballots, btarg \in Ballots
    <3> QED BY <1>tep, <1>bound, <1>baltarg
  <2> QED BY MessageInterfaceAssumptions, LearnerGraphAssumptions, <2>exhyp, <2>capemptyraw, OneBFreshDegenerate
<1> QED BY <1>caseNE, <1>caseE
====================================================================
