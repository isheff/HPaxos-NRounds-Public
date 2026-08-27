--------------------------- MODULE AsymmetricTermination ---------------------------
\* Termination over an arbitrary B^3 asymmetric quorum system, hypotheses in
\* asymmetric-trust vocabulary: learner alpha decides provided
\*   - alpha foresees the failure of everyone outside LiveAcceptors (i.e.,
\*     one of alpha's canonical quorums is entirely live), and
\*   - alpha foresees the failure of everyone outside SafeAcceptors (alpha is
\*     wise, giving the self-edge safety condition).
\* Both are DEPTH-ONE conditions: they mention only alpha's OWN fail-prone
\* sets, never the assumptions of alpha's quorum members.  With authentication
\* the depth recursion of the unauthenticated setting never starts.
EXTENDS HPaxosPlusCal, AsymmetricQuorums, AQQuorumChar, AQSafetyChar,
        AQSupportsAssumptions, Termination
LOCAL INSTANCE TLAPS

THEOREM AsymmetricTermination ==
  ASSUME MessageInterfaceAssumptions, ValueInterfaceAssumptions, AcceptorsAssumptions,
         NEW fps, AQTypeOK(fps), AQNonTrivial(fps), AQB3(fps), AQEmbedded(fps),
         IsFiniteSet(Acceptors), Acceptors # {},
         Spec, NetworkAssumption,
         NEW alpha \in Learners, NEW bal \in Ballots,
         AQWise(fps, alpha, Acceptors \ LiveAcceptors),
         AQWise(fps, alpha, Acceptors \ SafeAcceptors)
  PROVE  \E p \in Proposals :
           (( /\ \A x \in Proposals : (((<>KnownToLive(x)) /\ (B(x) > bal)) => (x = p))
              /\ <>(p \in Msgs)
              /\ TranFairness(p)
           ) => <> Decision(Msgs, alpha, B(p)))
<1>lga. LearnerGraphAssumptions  BY AQSupportsAssumptions
<1>fa. FiniteAcceptors  BY DEF FiniteAcceptors
<1>aa. alpha \in Acceptors  BY DEF AQEmbedded
<1>lsub. LiveAcceptors \in SUBSET Acceptors
  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption, LiveAcceptorsAssumption
<1>ssub. SafeAcceptors \in SUBSET Acceptors
  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption
<1>lq. LiveAcceptors \in Quorums(alpha)
  BY <1>aa, <1>lsub, <1>fa, AQQuorumChar
<1>lp. {alpha} \in LearnerPairs
  <2>1. <<alpha, alpha>> \in Learners \X Learners  OBVIOUS
  <2>2. {alpha, alpha} \in LearnerPairs  BY <2>1 DEF LearnerPairs
  <2> QED  BY <2>2
<1>jw. AQJointlyWise(fps, {alpha}, Acceptors \ SafeAcceptors)
  BY DEF AQJointlyWise
<1>ss. SafeAcceptors \in SafetySets({alpha})
  BY <1>lp, <1>ssub, <1>jw, <1>fa, AQSafetyChar
<1> QED
  BY <1>lga, <1>lq, <1>ss, Termination
====================================================================
