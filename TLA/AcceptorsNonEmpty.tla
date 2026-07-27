------------------------ MODULE AcceptorsNonEmpty ------------------------
\* Statement mentions LearnersNonEmpty, QuorumsNonEmpty, LearnersMightAgree,
\* ValidLearnerGraphAssumption and Acceptors -- all exported by
\* LearnerGraphInterface. The proof unfolds Quorums / LearnerPairs /
\* LearnersMightAgree / ValidLearnerGraphAssumption, also from there.
EXTENDS LearnerGraphInterface

LEMMA AcceptorsNonEmpty ==
  (/\ LearnersNonEmpty
   /\ QuorumsNonEmpty
   /\ LearnersMightAgree
   /\ ValidLearnerGraphAssumption
   ) => Acceptors # {}
<1> SUFFICES ASSUME LearnersNonEmpty, QuorumsNonEmpty,
                    LearnersMightAgree, ValidLearnerGraphAssumption
             PROVE Acceptors # {}
  OBVIOUS
<1>ne. Learners # {}  BY DEF LearnersNonEmpty
<1>1. PICK alpha \in Learners : TRUE  BY <1>ne
<1>2. Quorums(alpha) # {}  BY <1>1 DEF QuorumsNonEmpty
<1>3. PICK q \in Quorums(alpha) : TRUE  BY <1>2
<1>4. q \subseteq Acceptors  BY <1>3 DEF Quorums
<1>5. <<alpha, alpha>> \in Learners \X Learners  BY <1>1
<1>6. {alpha, alpha} \in LearnerPairs  BY <1>5 DEF LearnerPairs
<1>7. Acceptors \in SafetySets({alpha, alpha})  BY <1>6 DEF LearnersMightAgree
<1>8. Acceptors \cap q \cap q # {}  BY <1>1, <1>3, <1>7 DEF ValidLearnerGraphAssumption
<1>9. q # {}  BY <1>8
<1> QED BY <1>4, <1>9
====================================================================
