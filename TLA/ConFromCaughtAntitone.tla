---------------------- MODULE ConFromCaughtAntitone ----------------------
\* Statement mentions Learners and ConFromCaught; the proof also unfolds
\* SafetySets. All exported by LearnerGraphInterface.
\* ValidSeqLenBoundLearners cites this lemma, so these must be EXTENDS.
EXTENDS LearnerGraphInterface

\* ConFromCaught is antitone: a bigger caught set only disconnects more
\* learners (an uncaught safety set for the bigger caught set is a fortiori
\* uncaught for the smaller one).
LEMMA ConFromCaughtAntitone ==
  ASSUME NEW alpha \in Learners, NEW A, NEW B, A \subseteq B
  PROVE ConFromCaught(alpha, B) \subseteq ConFromCaught(alpha, A)
<1> SUFFICES ASSUME NEW beta \in ConFromCaught(alpha, B)
             PROVE beta \in ConFromCaught(alpha, A)
  OBVIOUS
<1>1. PICK s \in SafetySets({alpha, beta}) : s \cap B = {}  BY DEF ConFromCaught
<1>2. s \cap A \subseteq s \cap B  OBVIOUS
<1>3. s \cap A = {}  BY <1>1, <1>2
<1> QED BY <1>1, <1>3 DEF ConFromCaught
====================================================================
