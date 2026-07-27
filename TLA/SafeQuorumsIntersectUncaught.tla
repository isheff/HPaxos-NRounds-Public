------------------ MODULE SafeQuorumsIntersectUncaught ------------------
EXTENDS MessageInterface

\* The central witness-extraction step: two quorums for a connected pair of
\* learners intersect in an acceptor that is not caught -- inside the safety
\* set that witnesses the connection.
LEMMA SafeQuorumsIntersectUncaught ==
  ASSUME ValidLearnerGraphAssumption,
         NEW l1 \in Learners, NEW l2 \in Learners,
         NEW c,
         NEW s \in SafetySets({l1, l2}), s \cap c = {},
         NEW q1 \in Quorums(l1), NEW q2 \in Quorums(l2)
  PROVE \E a \in Acceptors : a \in q1 /\ a \in q2 /\ a \notin c
<1>1. s \cap q1 \cap q2 # {}  BY DEF ValidLearnerGraphAssumption
<1>2. PICK a \in s \cap q1 \cap q2 : TRUE  BY <1>1
<1>3. a \in s /\ a \in q1 /\ a \in q2  BY <1>2
<1>4. a \notin c
  <2> SUFFICES ASSUME a \in c PROVE FALSE  OBVIOUS
  <2>1. a \in s \cap c  BY <1>3
  <2> QED BY <2>1
<1>5. a \in Acceptors
  <2>1. q1 \subseteq Acceptors  BY DEF Quorums
  <2> QED BY <1>3, <2>1
<1> QED BY <1>3, <1>4, <1>5
====================================================================
