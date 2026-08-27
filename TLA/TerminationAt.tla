------------------------------ MODULE TerminationAt ------------------------------
\* Termination with the \A-over-temporal elimination done once, at bound
\* parameters, in a LEAN context: call sites with heavy ambients (record
\* literals, embedding equations) cite this by lemma application -- which
\* instantiates through machinery that works -- instead of eliminating
\* Termination's own quantifiers under their local clutter.
EXTENDS HPaxosPlusCal, Termination

\* Opaque wrapper for the conclusion: raw-temporal-conclusion lemmas only
\* apply at identity names; over the opaque symbol the application is
\* first-order and works at any concrete learner/ballot.
TermAtOp(alpha, bal) ==
  \E p \in Proposals :
    (( /\ \A x \in Proposals : (((<>KnownToLive(x)) /\ (B(x) > bal)) => (x = p))
       /\ <>(p \in Msgs)
       /\ TranFairness(p)
    ) => <> Decision(Msgs, alpha, B(p)))

LEMMA TerminationAt ==
  ASSUME MessageInterfaceAssumptions, ValueInterfaceAssumptions,
         LearnerGraphAssumptions, AcceptorsAssumptions,
         Spec, NetworkAssumption,
         NEW alpha \in Learners, NEW bal \in Ballots,
         LiveAcceptors \in Quorums(alpha),
         SafeAcceptors \in SafetySets({alpha})
  PROVE  TermAtOp(alpha, bal)
<1>lga. LearnerGraphAssumptions  OBVIOUS
<1>lq. LiveAcceptors \in Quorums(alpha)  OBVIOUS
<1>ss. SafeAcceptors \in SafetySets({alpha})  OBVIOUS
<1> QED  BY <1>lga, <1>lq, <1>ss, Termination DEF TermAtOp
====================================================================
