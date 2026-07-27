--------------------------- MODULE BetaStarExists ---------------------------
EXTENDS MessageInterface, FiniteSetTheorems,
        TopLearnerMsgCorrect, TranClosureClosed, BBallot, FiniteMaxExists

\* Picking beta*: the globally top-ballot per-learner witness. BXBeta is one
\* of the definitions kept in MessageInterface so FiniteMaxExists can be
\* applied to it as a NAMED operator.
LEMMA BetaStarExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mm \in SUBSET Messages, NEW SS \in SUBSET Learners, SS # {},
         \A beta \in SS : \E x \in TranClosure(mm) : beta \in Lrns(x),
         NEW bd \in Nat, \A x \in TranClosure(mm) : B(x) < bd
  PROVE \E beta \in SS : \A gamma \in SS : BXBeta(mm,gamma) <= BXBeta(mm,beta)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>fin. IsFiniteSet(SS)
  <2>1. IsFiniteSet(Learners)  BY DEF LearnerGraphAssumptions, FiniteLearners
  <2> QED BY <2>1, FS_Subset
<1>nat. \A beta \in SS : BXBeta(mm,beta) \in Nat
  <2> SUFFICES ASSUME NEW beta \in SS PROVE BXBeta(mm,beta) \in Nat  OBVIOUS
  <2>1. TopLearnerMsg(mm,beta) \in TranClosure(mm)  BY <1>mi, TopLearnerMsgCorrect
  <2>2. TopLearnerMsg(mm,beta) \in Messages  BY <2>1, <1>mi, TranClosureClosed
  <2>3. B(TopLearnerMsg(mm,beta)) \in Ballots  BY <2>2, <1>mi, BBallot
  <2> QED BY <2>3 DEF Ballots, BXBeta
<1> QED BY <1>fin, SS # {}, <1>nat, FiniteMaxExists
====================================================================
