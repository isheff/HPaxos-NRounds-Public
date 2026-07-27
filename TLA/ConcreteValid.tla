----------------------------- MODULE ConcreteValid -----------------------------
EXTENDS LearnerGraphConcrete, Fields, SafetyResolve, QuorumResolve,
        VL_LL, VL_RR, VL_CX, VL_XC

LEMMA ConcreteValid ==
  ASSUME LearnerGraphInterface = CLGI
  PROVE \A x \in Learners : \A y \in Learners :
          \A m  \in GetSpecifiedSafetySets({x,y}) :
          \A mx \in GetSpecifiedQuorums(x) :
          \A my \in GetSpecifiedQuorums(y) :
            (m \cap mx \cap my) # {}
  <1>L. Learners = CLrn BY Fields
  <1> SUFFICES ASSUME NEW x \in Learners, NEW y \in Learners,
                      NEW m  \in GetSpecifiedSafetySets({x,y}),
                      NEW mx \in GetSpecifiedQuorums(x),
                      NEW my \in GetSpecifiedQuorums(y)
               PROVE (m \cap mx \cap my) # {}
      OBVIOUS
  <1>1. x \in 1..4 /\ y \in 1..4 BY <1>L DEF CLrn
  <1>2. m \in (IF {x,y} \subseteq {1,2} THEN CLG ELSE IF {x,y} \subseteq {3,4} THEN CRG ELSE CCG)
      BY <1>1, SafetyResolve
  <1>3. mx \in (IF x \in {1,2} THEN CLQ ELSE CRQ) BY <1>1, QuorumResolve
  <1>4. my \in (IF y \in {1,2} THEN CLQ ELSE CRQ) BY <1>1, QuorumResolve
  <1>g. (x \in {1,2} \/ x \in {3,4}) /\ (y \in {1,2} \/ y \in {3,4}) BY <1>1
  <1>5. CASE x \in {1,2} /\ y \in {1,2}
    <2>1. {x,y} \subseteq {1,2} BY <1>5
    <2>2. m \in CLG BY <1>2, <2>1
    <2>3. mx \in CLQ /\ my \in CLQ BY <1>3, <1>4, <1>5
    <2> QED BY <2>2, <2>3, VL_LL
  <1>6. CASE x \in {3,4} /\ y \in {3,4}
    <2>0. ~({x,y} \subseteq {1,2}) BY <1>6
    <2>1. {x,y} \subseteq {3,4} BY <1>6
    <2>2. m \in CRG BY <1>2, <2>0, <2>1
    <2>3. mx \in CRQ /\ my \in CRQ BY <1>3, <1>4, <1>6
    <2> QED BY <2>2, <2>3, VL_RR
  <1>7. CASE x \in {1,2} /\ y \in {3,4}
    <2>0. ~({x,y} \subseteq {1,2}) BY <1>7
    <2>1. ~({x,y} \subseteq {3,4}) BY <1>7
    <2>2. m \in CCG BY <1>2, <2>0, <2>1
    <2>3. mx \in CLQ /\ my \in CRQ BY <1>3, <1>4, <1>7
    <2> QED BY <2>2, <2>3, VL_CX
  <1>8. CASE x \in {3,4} /\ y \in {1,2}
    <2>0. ~({x,y} \subseteq {1,2}) BY <1>8
    <2>1. ~({x,y} \subseteq {3,4}) BY <1>8
    <2>2. m \in CCG BY <1>2, <2>0, <2>1
    <2>3. mx \in CRQ /\ my \in CLQ BY <1>3, <1>4, <1>8
    <2> QED BY <2>2, <2>3, VL_XC
  <1> QED BY <1>g, <1>5, <1>6, <1>7, <1>8
=============================================================================
