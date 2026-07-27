------------------------ MODULE DecisionHighWitness ------------------------
\* MaxDepthFiniteAcceptors comes from the LearnerGraphInterface split; it and
\* MessageInterface share LearnerGraphInterface, so EXTENDS keeps one copy.
EXTENDS MessageInterface,
        QuorumsHaveMembers, TranClosureClosed,
        MaxDepthFiniteAcceptors, HasDepthLrns

\* Every decision (slow or fast) exhibits a closure message at the decision
\* ballot attested by the deciding learner: via any member of the slow
\* decision's nonempty MaxDepth quorum (HasDepthDownward + HasDepthLrns).
LEMMA DecisionHighWitness ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mset \in SUBSET Messages,
         NEW beta \in Learners, NEW b \in Ballots,
         Decision(mset, beta, b)
  PROVE \E M \in TranClosure(mset) : B(M) = b /\ beta \in Lrns(M)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lga. FiniteAcceptors /\ LearnersNonEmpty /\ QuorumsNonEmpty /\ LearnersMightAgree /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>1. CASE DecisionSlow(mset, beta, b)
  <2> DEFINE W == {x \in TranClosure(mset) : B(x) = b /\ HasDepth(beta, x, MaxDepth(beta))}
  <2>sigs. SigS(W) \in Quorums(beta)  BY <1>1 DEF DecisionSlow
  <2>ne. SigS(W) # {}  BY <2>sigs, <1>lga, QuorumsHaveMembers
  <2>Wne. W # {}  BY <2>ne DEF SigS
  <2> PICK M \in W : TRUE  BY <2>Wne
  <2>M. M \in TranClosure(mset) /\ B(M) = b /\ HasDepth(beta, M, MaxDepth(beta))  OBVIOUS
  <2>MMsg. M \in Messages  BY <2>M, <1>mi, TranClosureClosed
  <2>mdpos. MaxDepth(beta) \in 1..Cardinality(Acceptors)  BY <1>lga, MaxDepthFiniteAcceptors
  <2>mdge1. MaxDepth(beta) >= 1 /\ MaxDepth(beta) \in Nat  BY <2>mdpos
  <2>lrn. beta \in Lrns(M)  BY <2>M, <2>MMsg, <2>mdge1, <1>mi, <1>lga, HasDepthLrns
  <2> QED BY <2>M, <2>lrn
<1> QED BY <1>1 DEF Decision
====================================================================
