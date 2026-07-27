------------------ MODULE AgreementImpliesSelfAgreement ------------------
\* Statement mentions CondensedLearnerGraphAssumption, Learners, SafetySets,
\* all of which LearnerGraphInterface exports. Nothing else is needed: the
\* proof cites no theorems and no backend method operators.
EXTENDS LearnerGraphInterface

THEOREM AgreementImpliesSelfAgreement ==
  (CondensedLearnerGraphAssumption
   ) => \A alpha \in Learners: \A beta \in Learners:
   SafetySets({alpha, beta}) \subseteq SafetySets({alpha, alpha})
<1> SUFFICES ASSUME CondensedLearnerGraphAssumption,
                    NEW alpha \in Learners, NEW beta \in Learners
             PROVE SafetySets({alpha, beta}) \subseteq SafetySets({alpha, alpha})
  OBVIOUS
<1> SUFFICES ASSUME NEW s \in SafetySets({alpha, beta}) PROVE s \in SafetySets({alpha, alpha})  OBVIOUS
<1>1. s \in SafetySets({beta, alpha})  OBVIOUS
<1>2. s \cup s \in SafetySets({alpha, alpha})  BY <1>1 DEF CondensedLearnerGraphAssumption
<1>3. s \cup s = s  OBVIOUS
<1> QED BY <1>2, <1>3
====================================================================
