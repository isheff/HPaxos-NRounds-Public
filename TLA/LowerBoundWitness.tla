----------------------- MODULE LowerBoundWitness -----------------------
\* Statement mentions LearnersMightAgree / QuorumsNonEmpty /
\* ValidLearnerGraphAssumption / Learners / Acceptors / ValidSeqs
\* (LearnerGraphInterface); the proof also needs Seq and Len (Sequences).
\* Both MaxDepthFinite* lemmas cite this, so both are EXTENDS.
EXTENDS LearnerGraphInterface, Sequences

\* <<Acceptors,{}>> is always a valid chain of depth 1: ConFromCaught at
\* Acceptors is empty (no safety set is disjoint from all of Acceptors --
\* the empty set is ruled out as a safety set by ValidLearnerGraphAssumption
\* plus QuorumsNonEmpty), which differs from ConFromCaught at {} (all of
\* Learners, by LearnersMightAgree), given Learners is non-empty.
LEMMA LowerBoundWitness ==
  ASSUME LearnersMightAgree, QuorumsNonEmpty, ValidLearnerGraphAssumption,
         NEW alpha \in Learners, Acceptors # {}, Learners # {}
  PROVE <<Acceptors, {}>> \in ValidSeqs(alpha)
<1>seq. <<Acceptors, {}>> \in Seq(SUBSET Acceptors)  OBVIOUS
<1>full. \A beta \in Learners : Acceptors \in SafetySets({alpha, beta})
  <2> SUFFICES ASSUME NEW beta \in Learners PROVE Acceptors \in SafetySets({alpha, beta})  OBVIOUS
  <2>1. <<alpha, beta>> \in Learners \X Learners  OBVIOUS
  <2>2. {alpha, beta} \in LearnerPairs  BY <2>1 DEF LearnerPairs
  <2> QED BY <2>2 DEF LearnersMightAgree
<1>noempty. \A beta \in Learners : {} \notin SafetySets({alpha, beta})
  <2> SUFFICES ASSUME NEW beta \in Learners, {} \in SafetySets({alpha, beta})
               PROVE FALSE
    OBVIOUS
  <2>1. PICK q \in Quorums(alpha) : TRUE  BY DEF QuorumsNonEmpty
  <2>2. PICK r \in Quorums(beta) : TRUE  BY DEF QuorumsNonEmpty
  <2>3. ({} \cap q \cap r) # {}  BY <2>1, <2>2 DEF ValidLearnerGraphAssumption
  <2> QED BY <2>3
<1>con. ConFromCaught(alpha, Acceptors) = {}
  <2> SUFFICES ASSUME NEW beta \in ConFromCaught(alpha, Acceptors)
               PROVE FALSE
    OBVIOUS
  <2>1. PICK s \in SafetySets({alpha, beta}) : s \cap Acceptors = {}  BY DEF ConFromCaught
  <2>2. s \subseteq Acceptors  BY <2>1 DEF SafetySets
  <2>3. s = {}  BY <2>1, <2>2
  <2>4. beta \in Learners  BY DEF ConFromCaught
  <2> QED BY <2>1, <2>3, <2>4, <1>noempty
<1>con0. ConFromCaught(alpha, {}) = Learners
  <2>1. \A beta \in Learners : beta \in ConFromCaught(alpha, {})
    <3> SUFFICES ASSUME NEW beta \in Learners PROVE beta \in ConFromCaught(alpha, {})  OBVIOUS
    <3>1. Acceptors \in SafetySets({alpha, beta})  BY <1>full
    <3>2. Acceptors \cap {} = {}  OBVIOUS
    <3> QED BY <3>1, <3>2 DEF ConFromCaught
  <2> QED BY <2>1 DEF ConFromCaught
<1>diff. ConFromCaught(alpha, Acceptors) # ConFromCaught(alpha, {})  BY <1>con, <1>con0
<1>sub. {} \subseteq Acceptors  OBVIOUS
<1>idx. 1 .. (Len(<<Acceptors, {}>>) - 1) = {1}  OBVIOUS
<1>chain. \A i \in 1..(Len(<<Acceptors, {}>>)-1) :
             <<Acceptors, {}>>[i+1] \subseteq <<Acceptors, {}>>[i]
             /\ ConFromCaught(alpha, <<Acceptors, {}>>[i]) # ConFromCaught(alpha, <<Acceptors, {}>>[i+1])
  BY <1>idx, <1>sub, <1>diff
<1> QED BY <1>seq, <1>chain DEF ValidSeqs
====================================================================
