-------------------------- MODULE AgreementCaseLt --------------------------
EXTENDS MessageInterface,
        MaxDepthFiniteAcceptors, DecisionHighWitness,
        TraceExistenceSlow, TraceContradiction

\* Different ballots agree: extract himsg from the high decision
\* (DecisionHighWitness); the (slow) low decision gives TraceExistenceSlow;
\* instantiate at i = MaxDepth(alpha) and conclude by TraceContradiction.
LEMMA AgreementCaseLt ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         NEW lobal \in Ballots, NEW hibal \in Ballots,
         lobal < hibal,
         Decision(mset, alpha, lobal),
         Decision(mset, beta, hibal),
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset)))
  PROVE BalToVal(lobal) = BalToVal(hibal)
<1> SUFFICES ASSUME BalToVal(lobal) # BalToVal(hibal) PROVE FALSE  OBVIOUS
<1>lg. FiniteAcceptors /\ LearnersNonEmpty /\ QuorumsNonEmpty
       /\ LearnersMightAgree /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>md. MaxDepth(alpha) \in Nat
  <2>1. MaxDepth(alpha) \in 1..Cardinality(Acceptors)  BY <1>lg, MaxDepthFiniteAcceptors
  <2> QED BY <2>1
<1>mdin. MaxDepth(alpha) \in 0..MaxDepth(alpha)  BY <1>md
<1>hw. PICK himsg \in TranClosure(mset) : B(himsg) = hibal /\ beta \in Lrns(himsg)
  BY DecisionHighWitness
<1>slow. CASE DecisionSlow(mset, alpha, lobal)
  <2>ex. \A i \in 0..MaxDepth(alpha) :
           \E seq \in [1..i+1 -> TraceElem] :
             \A x \in 1..i+1 :
               /\ TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
               /\ TraceBudgetSlow(alpha, seq, x)
    BY <1>slow, <1>hw, TraceExistenceSlow
  <2>pick. PICK seq \in [1..MaxDepth(alpha)+1 -> TraceElem] :
             \A x \in 1..MaxDepth(alpha)+1 :
               /\ TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
               /\ TraceBudgetSlow(alpha, seq, x)
    BY <2>ex, <1>mdin
  <2>coremin. \A x \in 1..MaxDepth(alpha)+1 :
                TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
    BY <2>pick
  <2> QED BY <2>coremin, TraceContradiction
<1> QED BY <1>slow DEF Decision
====================================================================
