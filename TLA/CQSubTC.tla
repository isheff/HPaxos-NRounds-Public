------------------------------ MODULE CQSubTC ------------------------------
EXTENDS MessageInterface, CatchWitnessCorrect, TopLearnerMsgCorrect

LEMMA CQSubTC ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         NEW mm \in SUBSET Messages, NEW bd \in Nat,
         \A x \in TranClosure(mm) : B(x) < bd
  PROVE CQ(mm) \subseteq TranClosure(mm)
<1> SUFFICES ASSUME NEW z \in CQ(mm) PROVE z \in TranClosure(mm)  OBVIOUS
<1>1. \/ z \in {CatchWitness1(mm,s) : s \in CaughtAcc(mm)}
      \/ z \in {CatchWitness2(mm,s) : s \in CaughtAcc(mm)}
      \/ z \in {TopLearnerMsg(mm,beta) : beta \in RelevantLearners(mm)}
  BY DEF CQ
<1>a. CASE z \in {CatchWitness1(mm,s) : s \in CaughtAcc(mm)}
  <2> PICK s \in CaughtAcc(mm) : z = CatchWitness1(mm,s)  BY <1>a
  <2>cw. s \in CaughtS(TranClosure(mm))  BY DEF CaughtAcc
  <2> QED BY <2>cw, CatchWitnessCorrect
<1>b. CASE z \in {CatchWitness2(mm,s) : s \in CaughtAcc(mm)}
  <2> PICK s \in CaughtAcc(mm) : z = CatchWitness2(mm,s)  BY <1>b
  <2>cw. s \in CaughtS(TranClosure(mm))  BY DEF CaughtAcc
  <2> QED BY <2>cw, CatchWitnessCorrect
<1>d. CASE z \in {TopLearnerMsg(mm,beta) : beta \in RelevantLearners(mm)}
  <2> PICK beta \in RelevantLearners(mm) : z = TopLearnerMsg(mm,beta)  BY <1>d
  <2>ex. \E x \in TranClosure(mm) : beta \in Lrns(x)  BY DEF RelevantLearners
  <2> QED BY <2>ex, TopLearnerMsgCorrect
<1> QED BY <1>1, <1>a, <1>b, <1>d
====================================================================
