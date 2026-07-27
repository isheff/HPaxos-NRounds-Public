-------------------- MODULE AlwaysDecisionStableInvariant --------------------
EXTENDS HPaxosPlusCal, DecisionStableFixed

THEOREM AlwaysDecisionStableInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
  )=> []DecisionStableInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions
             PROVE []DecisionStableInvariant
  OBVIOUS
<1>fixed. \A alpha \in Learners : \A bal \in Ballots :
            [](Decision(Msgs, alpha, bal) => [](Decision(Msgs, alpha, bal)))
  BY DecisionStableFixed
<1> QED BY <1>fixed DEF DecisionStableInvariant
====================================================================
