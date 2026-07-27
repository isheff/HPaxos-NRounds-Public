-------------------- MODULE TerminatingProposalTwoAStepR --------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        TwoAStepLtProduceR, FiniteDiamond, DepthBridge
LOCAL INSTANCE TLAPS

\* Relaxed depth d -> d+1 step (clone of TerminatingProposalTwoAStep).
LEMMA TerminatingProposalTwoAStepR ==
  ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions,
         LearnerGraphAssumptions, AcceptorsAssumptions, NetworkAssumption,
         NEW alpha \in Learners, NEW allmessages \in SUBSET Messages,
         NEW bal \in Ballots, NEW p \in Proposals, NEW d \in Nat,
         d + 1 \in 1..MaxDepth(alpha), B(p) \in Ballots, B(p) > bal,
         LiveAcceptors \in Quorums(alpha),
         \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal)) =>
           ((V(x) = V(p)) /\ ((B(x) < B(p)) \/ (x = p)))),
         LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), d),
         IsAllMessagesEverSent(allmessages)
  PROVE  LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), d+1)
\* the per-acceptor TwoAStepLtOp facts, produced via TwoAStepLtProduceR
<1>prod. \A s \in LiveAcceptors : TwoAStepLtOp(allmessages, alpha, p, d, s)
  <2>1. IsAllMessagesEverSent(allmessages)
        => (\A s \in LiveAcceptors : TwoAStepLtOp(allmessages, alpha, p, d, s))
    BY TwoAStepLtProduceR
  <2> QED  BY <2>1
<1>lsub. LiveAcceptors \subseteq Acceptors
  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption, LiveAcceptorsAssumption
<1>lfin. IsFiniteSet(LiveAcceptors)
  BY <1>lsub, FS_Subset, FiniteAcceptors DEF FiniteAcceptors, LearnerGraphAssumptions
<1>ldsb. LiveAcceptors \subseteq SigS({x \in allmessages : B(x) = B(p) /\ HasDepth(alpha, x, d)})
  BY DEF LiveAcceptorsSentDepthBallot
<1>ch. \A aa \in LiveAcceptors :
         /\ (CHOOSE x \in allmessages : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))) \in allmessages
         /\ Sig(CHOOSE x \in allmessages : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))) = aa
  <2> SUFFICES ASSUME NEW aa \in LiveAcceptors
               PROVE  /\ (CHOOSE x \in allmessages : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))) \in allmessages
                      /\ Sig(CHOOSE x \in allmessages : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))) = aa
    OBVIOUS
  <2>ne. \E x \in allmessages : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))
    BY <1>ldsb DEF SigS
  <2> QED  BY <2>ne
<1>wsub. WPrimeStep(allmessages, alpha, p, d) \subseteq allmessages
  BY <1>ch DEF WPrimeStep
<1>wfin. IsFiniteSet(WPrimeStep(allmessages, alpha, p, d))
  BY <1>lfin, FS_Image DEF WPrimeStep
\* <>(WP subseteq Msgs): inline the FiniteDiamond argument
<1>dia. \A m \in WPrimeStep(allmessages, alpha, p, d) : DiaMem(m)
  <2> SUFFICES ASSUME NEW m \in WPrimeStep(allmessages, alpha, p, d) PROVE DiaMem(m)  OBVIOUS
  <2>mx. m \in allmessages  BY <1>wsub
  <2>1. \A mm : (mm \in allmessages <=> IAMESCond(mm))  BY DEF IsAllMessagesEverSent
  <2> HIDE DEF IAMESCond
  <2>bic. m \in allmessages <=> IAMESCond(m)  BY <2>1
  <2>cond. IAMESCond(m)  BY <2>mx, <2>bic
  <2> QED  BY <2>cond DEF DiaMem, IAMESCond
<1>fdhyp. FD_Hyp(WPrimeStep(allmessages, alpha, p, d))  BY <1>dia, <1>wfin DEF FD_Hyp
<1>fdgood. FD_Good(WPrimeStep(allmessages, alpha, p, d))  BY <1>fdhyp, FiniteDiamond
<1>ev. <>(WPrimeStep(allmessages, alpha, p, d) \subseteq Msgs)
  BY <1>fdgood DEF FD_Good, FD_Tgt
<1> SUFFICES ASSUME NEW s \in LiveAcceptors
             PROVE  s \in SigS({x \in allmessages : B(x) = B(p) /\ HasDepth(alpha, x, d+1)})
  BY DEF LiveAcceptorsSentDepthBallot
<1>lt0. TwoAStepLtOp(allmessages, alpha, p, d, s)  BY <1>prod
<1>ltc. (WPrimeStep(allmessages, alpha, p, d) \subseteq Msgs)
        ~> (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1))
  BY <1>lt0 DEF TwoAStepLtOp
<1>dia2. <>(\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1))
  BY <1>ev, <1>ltc, PTL
<1>br. \E twoa \in allmessages : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1)
  BY <1>dia2, DepthBridge
<1> QED  BY <1>br DEF SigS
====================================================================
