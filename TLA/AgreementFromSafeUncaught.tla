---------------------- MODULE AgreementFromSafeUncaught ----------------------
\* AgreementM comes from the MessageInterface split; it and HPaxosPlusCal
\* share MessageInterface, so it must be EXTENDS.
EXTENDS HPaxosPlusCal, NetworkTranClosureEq, AgreementM

LEMMA AgreementFromSafeUncaught ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         Inv, SafeAcceptorsUncaughtInvariant
  PROVE AgreementInvariant
<1> SUFFICES ASSUME NEW alpha \in Learners, NEW beta \in Learners,
                    NEW alphabal \in Ballots, NEW betabal \in Ballots,
                    SafeAcceptors \in SafetySets({alpha, beta}),
                    Decision(Msgs, alpha, alphabal),
                    Decision(Msgs, beta, betabal)
             PROVE BalToVal(alphabal) = BalToVal(betabal)
  BY DEF AgreementInvariant
<1>tc. TranClosure(Msgs) = Msgs  BY NetworkTranClosureEq
<1>unc. SafeAcceptors \cap CaughtS(Msgs) = {}  BY DEF SafeAcceptorsUncaughtInvariant
<1>con. alpha \in ConFromCaught(beta, CaughtS(TranClosure(Msgs)))
  BY <1>tc, <1>unc DEF ConFromCaught
<1>netsub. Msgs \in SUBSET Messages  BY DEF Inv
<1> QED BY <1>con, <1>netsub, AgreementM
====================================================================
