------------------------- MODULE DecisionStableFixed -------------------------
EXTENDS HPaxosPlusCal, DecisionOneStep, InvHolds
LOCAL INSTANCE TLAPS

LEMMA DecisionStableFixed ==
  ASSUME LearnerGraphAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots
  PROVE Spec => [](Decision(Msgs, alpha, bal) => [](Decision(Msgs, alpha, bal)))
<1>1. Inv /\ [Next]_vars /\ Decision(Msgs,alpha,bal) => Decision(Msgs,alpha,bal)'  BY DecisionOneStep
<1>2. Spec => []Inv  BY InvHolds
<1> QED BY <1>1, <1>2, PTL DEF Spec
====================================================================
