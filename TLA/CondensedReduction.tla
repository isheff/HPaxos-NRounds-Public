-------------------------- MODULE CondensedReduction --------------------------
\* FiniteSetTheorems by EXTENDS (never LOCAL INSTANCE): FS_Subset is cited below,
\* and its FiniteSets must be the SAME copy the statement's IsFiniteSet comes from.
EXTENDS LearnerGraphConcrete, FiniteSetTheorems

LEMMA CondensedReduction ==
  ASSUME IsFiniteSet(Acceptors),
         \A x \in Learners : \A y \in Learners : \A z \in Learners :
           \A m1 \in GetSpecifiedSafetySets({x,y}) :
           \A m2 \in GetSpecifiedSafetySets({y,z}) :
             \E m3 \in GetSpecifiedSafetySets({x,z}) : m3 \subseteq (m1 \cup m2)
  PROVE  CondensedLearnerGraphAssumption
  <1> SUFFICES ASSUME NEW x \in Learners, NEW y \in Learners, NEW z \in Learners,
                      NEW xy \in SafetySets({x,y}), NEW yz \in SafetySets({y,z})
               PROVE (xy \cup yz) \in SafetySets({x,z})
      BY DEF CondensedLearnerGraphAssumption
  <1>1. PICK m1 \in GetSpecifiedSafetySets({x,y}) : m1 \subseteq xy BY DEF SafetySets
  <1>2. PICK m2 \in GetSpecifiedSafetySets({y,z}) : m2 \subseteq yz BY DEF SafetySets
  <1>3. PICK m3 \in GetSpecifiedSafetySets({x,z}) : m3 \subseteq (m1 \cup m2) BY <1>1, <1>2
  <1>4. xy \subseteq Acceptors /\ yz \subseteq Acceptors BY DEF SafetySets
  <1>5. (xy \cup yz) \subseteq Acceptors BY <1>4
  <1>6. IsFiniteSet(xy \cup yz) BY <1>5, FS_Subset
  <1>7. m3 \subseteq (xy \cup yz) BY <1>1, <1>2, <1>3
  <1> QED BY <1>5, <1>6, <1>7 DEF SafetySets
=============================================================================
