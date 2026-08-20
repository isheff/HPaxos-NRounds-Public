------------------- MODULE TerminatingProposalFreshOneBsR -------------------
EXTENDS HPaxosPlusCal, HighNowBox, LowNowBox, AmNowBox,
        DepthZeroLeadsToRW, DepthZeroBridge, KnownDiaMem, QuorumsHaveMembers
LOCAL INSTANCE TLAPS

\* Relaxed depth-0 base case: every live acceptor eventually sends a fresh
\* ballot-B(p) depth-0 message (into the ever-sent set).
LEMMA TerminatingProposalFreshOneBsR ==
  ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions,
         LearnerGraphAssumptions, AcceptorsAssumptions, NetworkAssumption,
         NEW alpha \in Learners, NEW allmessages \in SUBSET Messages,
         NEW bal \in Ballots, NEW p \in Proposals, TranFairness(p),
         NEW M, M = {mm \in allmessages : B(mm) <= bal},
         DecideableProposalTranExclusive(M) \subseteq Tran(p),
         V(p) = DecideableProposalV(alpha, bal, M),
         B(p) > bal, Sig(p) \notin Acceptors,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(M))),
         \A x \in TranClosure(M) : B(x) <= bal,
         ConFromCaught(alpha, CaughtS({ww \in allmessages : B(ww) < B(p)}))
           = ConFromCaught(alpha, CaughtS(TranClosure(M))),
         LiveAcceptors \in Quorums(alpha),
         \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal)) =>
           ((V(x) = V(p)) /\ ((B(x) < B(p)) \/ (x = p)))),
         p \in allmessages,
         IsAllMessagesEverKnown(allmessages)
  PROVE  LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), 0)
<1>mmsg. M \in SUBSET Messages  OBVIOUS
<1>lg. LearnersMightAgree /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>lne. LiveAcceptors # {}  BY <1>lg, QuorumsHaveMembers
<1>high. []HighNowT(p, bal)  BY <1>lne, HighNowBox
<1>low. []LowNowT(bal, M)  BY <1>lne, LowNowBox
<1>amb. []AmNowT(allmessages)  BY <1>lne, AmNowBox
<1> SUFFICES ASSUME NEW a \in LiveAcceptors
             PROVE  a \in SigS({x \in allmessages : B(x) = B(p) /\ HasDepth(alpha, x, 0)})
  BY DEF LiveAcceptorsSentDepthBallot
<1>pnet. <>(p \in Msgs)
  <2>1. Spec => (IsAllMessagesEverKnown(allmessages)
                 => (p \in allmessages => DiaMem(p)))
    BY KnownDiaMem
  <2> QED  BY <2>1 DEF DiaMem
<1>hyp. DZLTHypR(alpha, bal, M, p, allmessages)
  BY <1>high, <1>low, <1>amb DEF DZLTHypR
<1>dz. (Spec /\ TranFairness(p))
       => ((p \in Msgs) ~> (\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)))
  BY <1>mmsg, <1>hyp, DepthZeroLeadsToRW
<1>lt. (p \in Msgs) ~> (\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
  BY <1>dz
<1>dia. <>(\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
  BY <1>lt, <1>pnet, PTL
<1>br. \E y \in allmessages : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)
  BY <1>dia, DepthZeroBridge
<1> QED  BY <1>br DEF SigS
====================================================================
