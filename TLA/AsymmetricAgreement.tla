---------------------------- MODULE AsymmetricAgreement ----------------------------
\* Agreement over an arbitrary B^3 asymmetric quorum system, with the
\* hypothesis phrased in asymmetric-trust vocabulary: two learners agree
\* whenever they are JOINTLY WISE about the actual faulty set (each foresees
\* the failure of everyone outside SafeAcceptors).  Instantiates
\* AlwaysAgreementInvariant through the wisdom dictionary.
EXTENDS HPaxosPlusCal, AsymmetricQuorums, AQSafetyChar,
        AQSupportsAssumptions, AlwaysAgreementInvariant
LOCAL INSTANCE TLAPS

THEOREM AsymmetricAgreement ==
  ASSUME MessageInterfaceAssumptions, ValueInterfaceAssumptions, AcceptorsAssumptions,
         NEW fps, AQTypeOK(fps), AQNonTrivial(fps), AQB3(fps), AQEmbedded(fps),
         IsFiniteSet(Acceptors), Acceptors # {},
         NEW alpha \in Learners, NEW beta \in Learners,
         AQJointlyWise(fps, {alpha, beta}, Acceptors \ SafeAcceptors)
  PROVE  Spec => [](\A alphabal \in Ballots : \A betabal \in Ballots :
                      (Decision(Msgs, alpha, alphabal) /\ Decision(Msgs, beta, betabal))
                        => BalToVal(alphabal) = BalToVal(betabal))
<1>lga. LearnerGraphAssumptions  BY AQSupportsAssumptions
<1>fa. FiniteAcceptors  BY DEF FiniteAcceptors
<1>lp. {alpha, beta} \in LearnerPairs
  <2>1. <<alpha, beta>> \in Learners \X Learners  OBVIOUS
  <2> QED  BY <2>1 DEF LearnerPairs
<1>ssub. SafeAcceptors \in SUBSET Acceptors
  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption
<1>ss. SafeAcceptors \in SafetySets({alpha, beta})
  BY <1>lp, <1>ssub, <1>fa, AQSafetyChar
<1>inst. AgreementInvariant =>
           (\A alphabal \in Ballots : \A betabal \in Ballots :
              (Decision(Msgs, alpha, alphabal) /\ Decision(Msgs, beta, betabal))
                => BalToVal(alphabal) = BalToVal(betabal))
  BY <1>ss DEF AgreementInvariant
<1>box. Spec => []AgreementInvariant  BY <1>lga, AlwaysAgreementInvariant
<1> QED  BY <1>box, <1>inst, PTL
====================================================================
