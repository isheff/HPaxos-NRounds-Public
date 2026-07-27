---------------------------- MODULE ValidReduction ----------------------------
EXTENDS LearnerGraphConcrete

LEMMA ValidReduction ==
  ASSUME \A x \in Learners : \A y \in Learners :
           \A m  \in GetSpecifiedSafetySets({x,y}) :
           \A mx \in GetSpecifiedQuorums(x) :
           \A my \in GetSpecifiedQuorums(y) :
             (m \cap mx \cap my) # {}
  PROVE  ValidLearnerGraphAssumption
  <1> SUFFICES ASSUME NEW x \in Learners, NEW y \in Learners,
                      NEW s \in SafetySets({x,y}), NEW qx \in Quorums(x), NEW qy \in Quorums(y)
               PROVE (s \cap qx \cap qy) # {}
      BY DEF ValidLearnerGraphAssumption
  <1>1. PICK m  \in GetSpecifiedSafetySets({x,y}) : m  \subseteq s  BY DEF SafetySets
  <1>2. PICK mx \in GetSpecifiedQuorums(x)        : mx \subseteq qx BY DEF Quorums
  <1>3. PICK my \in GetSpecifiedQuorums(y)        : my \subseteq qy BY DEF Quorums
  <1>4. (m \cap mx \cap my) # {}                  BY <1>1, <1>2, <1>3
  <1>5. (m \cap mx \cap my) \subseteq (s \cap qx \cap qy) BY <1>1, <1>2, <1>3
  <1> QED BY <1>4, <1>5
=============================================================================
