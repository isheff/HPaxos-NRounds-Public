-------------------- MODULE ConFromCaughtCondensedTrans --------------------
EXTENDS MessageInterface

\* Connectivity is transitive on a condensed learner graph: the union of an
\* uncaught {alpha,beta} safety set and an uncaught {beta,gamma} safety set
\* is an uncaught {alpha,gamma} safety set.
LEMMA ConFromCaughtCondensedTrans ==
  ASSUME CondensedLearnerGraphAssumption,
         NEW alpha \in Learners, NEW beta \in Learners, NEW gamma \in Learners,
         NEW c,
         beta \in ConFromCaught(alpha, c),
         gamma \in ConFromCaught(beta, c)
  PROVE gamma \in ConFromCaught(alpha, c)
<1>1. PICK s1 \in SafetySets({alpha, beta}) : s1 \cap c = {}  BY DEF ConFromCaught
<1>2. PICK s2 \in SafetySets({beta, gamma}) : s2 \cap c = {}  BY DEF ConFromCaught
<1>3. (s1 \cup s2) \in SafetySets({alpha, gamma})  BY <1>1, <1>2 DEF CondensedLearnerGraphAssumption
<1>4. (s1 \cup s2) \cap c = {}  BY <1>1, <1>2
<1> QED BY <1>3, <1>4 DEF ConFromCaught
====================================================================
