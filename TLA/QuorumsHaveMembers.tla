------------------------ MODULE QuorumsHaveMembers ------------------------
EXTENDS MessageInterface

\* Every quorum has a member (intersect it with itself through the
\* Acceptors safety set).
LEMMA QuorumsHaveMembers ==
  ASSUME LearnersMightAgree, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, NEW q \in Quorums(alpha)
  PROVE q # {}
<1>1. <<alpha, alpha>> \in Learners \X Learners  OBVIOUS
<1>2. {alpha, alpha} \in LearnerPairs  BY <1>1 DEF LearnerPairs
<1>3. Acceptors \in SafetySets({alpha, alpha})  BY <1>2 DEF LearnersMightAgree
<1>4. Acceptors \cap q \cap q # {}  BY <1>3 DEF ValidLearnerGraphAssumption
<1> QED BY <1>4
====================================================================
