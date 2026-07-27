---------------------- MODULE ConFromCaughtAllCaught ----------------------
EXTENDS MessageInterface

\* With everything caught, no one is connected: an uncaught safety set would
\* have to be empty, and empty safety sets are ruled out by
\* ValidLearnerGraphAssumption.
THEOREM ConFromCaughtAllCaught ==
  ASSUME QuorumsNonEmpty, ValidLearnerGraphAssumption, NEW alpha \in Learners
  PROVE ConFromCaught(alpha, Acceptors) = {}
<1>noempty. \A beta \in Learners : {} \notin SafetySets({alpha, beta})
  <2> SUFFICES ASSUME NEW beta \in Learners, {} \in SafetySets({alpha, beta})
               PROVE FALSE
    OBVIOUS
  <2>1. PICK q \in Quorums(alpha) : TRUE  BY DEF QuorumsNonEmpty
  <2>2. PICK r \in Quorums(beta) : TRUE  BY DEF QuorumsNonEmpty
  <2>3. ({} \cap q \cap r) # {}  BY <2>1, <2>2 DEF ValidLearnerGraphAssumption
  <2> QED BY <2>3
<1> SUFFICES ASSUME ConFromCaught(alpha, Acceptors) # {} PROVE FALSE  OBVIOUS
<1>1. PICK beta \in ConFromCaught(alpha, Acceptors) : TRUE  OBVIOUS
<1>2. beta \in Learners  BY <1>1 DEF ConFromCaught
<1>3. PICK s \in SafetySets({alpha, beta}) : s \cap Acceptors = {}  BY <1>1 DEF ConFromCaught
<1>4. s \subseteq Acceptors  BY <1>3 DEF SafetySets
<1>5. s = {}  BY <1>3, <1>4
<1> QED BY <1>3, <1>5, <1>2, <1>noempty
====================================================================
