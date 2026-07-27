---------------------- MODULE ConcreteLearnersMightAgree ----------------------
EXTENDS LearnerGraphConcrete, Fields, SafetyResolve, FiniteSetTheorems

LEMMA ConcreteLearnersMightAgree == ASSUME LearnerGraphInterface = CLGI PROVE LearnersMightAgree
  <1> SUFFICES ASSUME NEW p \in LearnerPairs PROVE Acceptors \in SafetySets(p)
    BY DEF LearnersMightAgree
  <1>L. Learners = CLrn BY Fields
  <1>acc. Acceptors = CAcc BY Fields
  <1> PICK pr \in Learners \X Learners : p = {pr[1], pr[2]} BY DEF LearnerPairs
  <1> DEFINE x == pr[1]
  <1> DEFINE y == pr[2]
  <1>xy. x \in Learners /\ y \in Learners OBVIOUS
  <1>2. x \in 1..4 /\ y \in 1..4 BY <1>xy, <1>L DEF CLrn
  <1>3. GetSpecifiedSafetySets({x,y}) =
          IF {x,y} \subseteq {1,2} THEN CLG ELSE IF {x,y} \subseteq {3,4} THEN CRG ELSE CCG
    BY <1>2, SafetyResolve
  <1>4. GetSpecifiedSafetySets(p) # {}
    <2>1. CLG # {} BY DEF CLG
    <2>2. CRG # {} BY DEF CRG
    <2>3. CCG # {} BY DEF CCG
    <2> QED BY <1>3, <2>1, <2>2, <2>3
  <1>5. PICK m \in GetSpecifiedSafetySets(p) : TRUE BY <1>4
  <1>6. m \subseteq Acceptors
    <2>1. m \subseteq CAcc BY <1>3, <1>5 DEF CLG, CRG, CCG, CAcc
    <2> QED BY <2>1, <1>acc
  <1>7. IsFiniteSet(Acceptors)
    <2>1. IsFiniteSet(CAcc) BY FS_Interval DEF CAcc
    <2> QED BY <1>acc, <2>1
  <1>8. Acceptors \in SafetySets(p)
    <2>1. \E mm \in GetSpecifiedSafetySets(p) : mm \subseteq Acceptors BY <1>5, <1>6
    <2> QED BY <1>7, <2>1 DEF SafetySets
  <1> QED BY <1>8
=============================================================================
