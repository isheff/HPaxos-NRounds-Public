----------------- MODULE TerminatingProposalTwoAInductionR -----------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems, NaturalsInduction,
        MaxDepthFiniteAcceptors,
        TerminatingProposalFreshOneBsR, TerminatingProposalTwoAStepR
\* IsaM("blast") below is a TLAPS backend pragma: tlapm knows it natively, but
\* SANY only sees it as an operator if the TLAPS module is in scope.
LOCAL INSTANCE TLAPS

\* Relaxed bounded induction d = 0 .. MaxDepth(alpha).
LEMMA TerminatingProposalTwoAInductionR ==
  ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions,
         LearnerGraphAssumptions, AcceptorsAssumptions, NetworkAssumption,
         NEW alpha \in Learners, NEW allmessages \in SUBSET Messages,
         NEW bal \in Ballots, NEW p \in Proposals, TranFairness(p),
         NEW M, M = {m \in allmessages : B(m) <= bal},
         DecideableProposalTranExclusive(M) \subseteq Tran(p),
         V(p) = DecideableProposalV(alpha, bal, M),
         B(p) > bal, Sig(p) \notin Acceptors,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(M))),
         \A x \in TranClosure(M) : B(x) <= bal,
         ConFromCaught(alpha, CaughtS({ww \in allmessages : B(ww) < B(p)}))
           = ConFromCaught(alpha, CaughtS(TranClosure(M))),
         B(p) \in Ballots,
         LiveAcceptors \in Quorums(alpha),
         \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal)) =>
           ((V(x) = V(p)) /\ ((B(x) < B(p)) \/ (x = p)))),
         p \in allmessages,
         IsAllMessagesEverSent(allmessages)
  PROVE  \A d \in 0..MaxDepth(alpha) : LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), d)
<1>lg. /\ FiniteAcceptors /\ LearnersNonEmpty /\ QuorumsNonEmpty
       /\ LearnersMightAgree /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>mdrange. MaxDepth(alpha) \in 1..Cardinality(Acceptors)  BY <1>lg, MaxDepthFiniteAcceptors
<1>facc. IsFiniteSet(Acceptors)  BY DEF FiniteAcceptors, LearnerGraphAssumptions
<1>cardnat. Cardinality(Acceptors) \in Nat  BY <1>facc, FS_CardinalityType
<1>mdn. MaxDepth(alpha) \in Nat  BY <1>mdrange, <1>cardnat
<1> DEFINE Q(n) == (n \in 0..MaxDepth(alpha))
                   => LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), n)
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A m2 \in 0..(n-1) : Q(m2)) => Q(n)
  <2> USE DEF Q
  <2> SUFFICES ASSUME NEW n \in Nat, \A m2 \in 0..(n-1) : Q(m2) PROVE Q(n)  OBVIOUS
  <2> SUFFICES ASSUME n \in 0..MaxDepth(alpha)
               PROVE  LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), n)
    OBVIOUS
  <2>c0. CASE n = 0
    BY <2>c0, TerminatingProposalFreshOneBsR
  <2>cn. CASE n # 0
    <3>n1. n - 1 \in Nat  BY <2>cn
    <3>n1in. n - 1 \in 0..(n-1)  BY <3>n1
    <3>qn1. Q(n - 1)  BY <3>n1in
    <3>n1md. (n - 1) \in 0..MaxDepth(alpha)  BY <1>mdn, <2>cn
    <3>pn1. LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), n - 1)  BY <3>qn1, <3>n1md
    <3>d1. (n - 1) + 1 \in 1..MaxDepth(alpha)  BY <1>mdn, <2>cn
    <3>pn. LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), (n - 1) + 1)
      BY <3>pn1, <3>d1, <3>n1, TerminatingProposalTwoAStepR
    <3>eq. (n - 1) + 1 = n  BY <2>cn
    <3> QED  BY <3>pn, <3>eq
  <2> QED  BY <2>c0, <2>cn
<1>allq. \A n \in Nat : Q(n)  BY <1>ind, GeneralNatInduction, IsaM("blast")
<1> SUFFICES ASSUME NEW d \in 0..MaxDepth(alpha)
             PROVE  LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), d)
  OBVIOUS
<1>dnat. d \in Nat  BY <1>mdn
<1>qd. Q(d)  BY <1>allq, <1>dnat
<1> QED  BY <1>qd DEF Q
====================================================================
