--------------------------- MODULE DecisionOneStep ---------------------------
EXTENDS HPaxosPlusCal, NetMono, InvStep, DecisionMono

LEMMA DecisionOneStep ==
  ASSUME LearnerGraphAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots
  PROVE Inv /\ [Next]_vars /\ Decision(Msgs, alpha, bal) => Decision(Msgs, alpha, bal)'
<1> SUFFICES ASSUME Inv, [Next]_vars, Decision(Msgs, alpha, bal)
             PROVE Decision(Msgs, alpha, bal)'
  OBVIOUS
<1>netsub. Msgs \in SUBSET Messages  BY DEF Inv
<1>net. Msgs \subseteq Msgs'  BY NetMono
<1>invp. Inv'  BY InvStep
<1>netsub2. Msgs' \in SUBSET Messages  BY <1>invp DEF Inv
<1>dm. Decision(Msgs', alpha, bal)  BY <1>netsub, <1>netsub2, <1>net, DecisionMono
<1> QED BY <1>dm
====================================================================
