---------------------------- MODULE DecisionMono ----------------------------
\* Decision == DecisionSlow only (DecisionFast was dropped from Decision
\* upstream in MessageInterface), so monotonicity only needs the DecisionSlow /
\* quorum-upward-closure argument.
EXTENDS HPaxosPlusCal, FiniteSetTheorems, TranClosureMono, QuorumUpward

LEMMA DecisionMono ==
  ASSUME LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW mp \in SUBSET Messages, m \subseteq mp,
         NEW alpha \in Learners, NEW bal \in Ballots,
         Decision(m, alpha, bal)
  PROVE Decision(mp, alpha, bal)
<1>fa. FiniteAcceptors  BY DEF LearnerGraphAssumptions
<1>tcm. TranClosure(m) \subseteq TranClosure(mp)  BY TranClosureMono
<1>slow. DecisionSlow(m,alpha,bal)  BY DEF Decision
<1> DEFINE W == {x \in TranClosure(m) : B(x) = bal /\ HasDepth(alpha, x, MaxDepth(alpha))}
<1> DEFINE Wp == {x \in TranClosure(mp) : B(x) = bal /\ HasDepth(alpha, x, MaxDepth(alpha))}
<1>quo. SigS(W) \in Quorums(alpha)  BY <1>slow DEF DecisionSlow
<1>sub. W \subseteq Wp  BY <1>tcm
<1>sigsub. SigS(W) \subseteq SigS(Wp)  BY <1>sub DEF SigS
<1>acc. SigS(Wp) \subseteq Acceptors
  <2> SUFFICES ASSUME NEW aa \in SigS(Wp) PROVE aa \in Acceptors  OBVIOUS
  <2>1. PICK y \in Wp : aa = Sig(y)  BY DEF SigS
  <2>2. HasDepth(alpha, y, MaxDepth(alpha))  BY <2>1
  <2> QED BY <2>2, <2>1 DEF HasDepth
<1>finacc. IsFiniteSet(Acceptors)  BY <1>fa DEF FiniteAcceptors
<1>fin. IsFiniteSet(SigS(Wp))  BY <1>acc, <1>finacc, FS_Subset
<1>up. SigS(Wp) \in Quorums(alpha)  BY <1>quo, <1>sigsub, <1>acc, <1>fin, QuorumUpward
<1> QED BY <1>up DEF DecisionSlow, Decision
====================================================================
