----------------------------- MODULE DecisionFastDImpossible -----------------------------
\* CONJECTURE, STATED WITHOUT PROOF.  The theorem below has no proof body, so
\* tlapm generates ZERO obligations for this module: a sweep reports it as
\* "All 0 obligation proved" and it is easy to mistake for a proven result.
EXTENDS MessageInterface
LOCAL INSTANCE TLAPS

THEOREM DecisionFastDImpossible ==
  \A d \in Nat : \* for ever depth of fast decision
  \E LGI : \* there is a learner graph
  (LGI = LearnerGraphInterface) => \* if we use that learner graph
  (/\ LearnerGraphAssumptions \* it will be valid and whatnot
   /\ (/\ MessageInterfaceAssumptions \* and if we use an acceptable set of messages
       /\ ValueInterfaceAssumptions \* and multiple valid values
       /\ \E vs \in SUBSET Values : (IsFiniteSet(vs) /\ Cardinality(vs) > 1)
      ) => \E m \in Messages : \* there is a messsage encapsulating decisions:
           \E b1 \in Ballots :
           \E b2 \in Ballots :
           \E alpha \in Learners : \* for some learner alpha
           (/\ DecisionFastD({m}, b1, d) \* a fast decision at b1
            /\ DecisionSlow({m}, alpha, b2) \* and a slow decision at b2
            /\ alpha \in Con(alpha, m) \* alpha must agree with itself
            /\ BalToVal(b1) # BalToVal(b2))) \* but it does not
====================================================================
