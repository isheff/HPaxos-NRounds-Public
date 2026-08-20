-------------------------- MODULE DepthZeroLeadsToR --------------------------
EXTENDS HPaxosPlusCal, KnowLeadsToTranW, DepthZeroKnownImpliesSentR
LOCAL INSTANCE TLAPS

\* Relaxed Step-5 leads-to: once p is on the network, live acceptor a
\* eventually has a sent depth-0 message at B(p).
LEMMA DepthZeroLeadsToR ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions, ValueInterfaceAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         \A x \in TranClosure(m) : B(x) <= bal,
         NEW p \in Proposals,
         DecideableProposalTranExclusive(m) \subseteq Tran(p),
         B(p) > bal,
         Sig(p) \notin Acceptors,
         V(p) = DecideableProposalV(alpha, bal, m),
         NEW am \in SUBSET Messages,
         ConFromCaught(alpha, CaughtS({ww \in am : B(ww) < B(p)}))
           = ConFromCaught(alpha, CaughtS(TranClosure(m))),
         []HighNowT(p, bal),
         []LowNowT(bal, m),
         []AmNowT(am),
         NEW a \in LiveAcceptors
  PROVE (Spec /\ TranFairness(p)) =>
        ((p \in Msgs) ~> (\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)))
<1>pmsg. p \in Messages
  BY MessageInterfaceAssumptions DEF MessageInterfaceAssumptions, TypeOKMessageInterface
<1>ptp. p \in Tran(p)  BY DEF Tran
<1>kltop. KLTT(p, a, p)  BY <1>pmsg, <1>ptp, KnowLeadsToTranW
<1>klt. (Spec /\ TranFairness(p)) => ((p \in Msgs) ~> (p \in known_messages[a]))
  BY <1>kltop DEF KLTT
<1>inv. Spec => [](p \in known_messages[a] =>
                     \E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
  BY DepthZeroKnownImpliesSentR
<1> QED BY <1>klt, <1>inv, PTL
====================================================================
