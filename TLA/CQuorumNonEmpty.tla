---------------------------- MODULE CQuorumNonEmpty ----------------------------
EXTENDS MessageConcrete

LEMMA CQuorumNonEmpty ==
  ASSUME LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW q \in Quorums(alpha)
  PROVE q # {}
<1>1. q \subseteq Acceptors  BY DEF Quorums
<1>2. Acceptors \in SafetySets({alpha,alpha})  BY DEF LearnersMightAgree, LearnerPairs
<1>3. (Acceptors \cap q \cap q) # {}  BY <1>2 DEF ValidLearnerGraphAssumption
<1>4. Acceptors \cap q \cap q = q  BY <1>1
<1> QED BY <1>3, <1>4
=============================================================================
