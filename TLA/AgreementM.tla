----------------------------- MODULE AgreementM -----------------------------
\* The safety result the whole MessageInterface development builds toward.
EXTENDS MessageInterface, ConFromCaughtSym, AgreementCaseLt

\* AgreementM assembles by trichotomy on the ballots: equal ballots agree
\* definitionally (values are a function of the ballot); alphabal < betabal
\* is AgreementCaseLt with the connection hypothesis reoriented by
\* ConFromCaughtSym; betabal < alphabal is AgreementCaseLt with the roles
\* swapped.
THEOREM AgreementM ==
  (/\ MessageInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ ValueInterfaceAssumptions) =>
    \A alpha \in Learners :
    \A beta \in Learners :
    \A m \in SUBSET Messages :
    \A alphabal \in Ballots :
    \A betabal \in Ballots :
    (/\ Decision(m, alpha, alphabal)
     /\ Decision(m, beta,  betabal )
     /\ alpha \in ConFromCaught(beta, CaughtS(TranClosure(m)))
    )=> BalToVal(alphabal) = BalToVal(betabal)
<1> SUFFICES ASSUME MessageInterfaceAssumptions,
                    LearnerGraphAssumptions,
                    ValueInterfaceAssumptions,
                    NEW alpha \in Learners, NEW beta \in Learners,
                    NEW m \in SUBSET Messages,
                    NEW alphabal \in Ballots, NEW betabal \in Ballots,
                    Decision(m, alpha, alphabal),
                    Decision(m, beta, betabal),
                    alpha \in ConFromCaught(beta, CaughtS(TranClosure(m)))
             PROVE BalToVal(alphabal) = BalToVal(betabal)
  OBVIOUS
<1>sym. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
  BY ConFromCaughtSym
<1>a. CASE alphabal < betabal
  <2> QED BY <1>a, <1>sym, AgreementCaseLt
<1>b. CASE betabal < alphabal
  <2>1. BalToVal(betabal) = BalToVal(alphabal)  BY <1>b, AgreementCaseLt
  <2> QED BY <2>1
<1>c. CASE alphabal = betabal
  <2> QED BY <1>c
<1>tri. alphabal < betabal \/ betabal < alphabal \/ alphabal = betabal
  BY DEF Ballots
<1> QED BY <1>a, <1>b, <1>c, <1>tri
====================================================================
