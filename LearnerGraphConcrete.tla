------------------------- MODULE LearnerGraphConcrete -------------------------
\* A concrete 4-learner / 9-acceptor learner graph realizing the partitions
\* {12|34}, {1234}, {1|2|3|4}, proven to satisfy LearnerGraphAssumptions.
EXTENDS LearnerGraphInterface
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetTheorems

\* ---- the concrete model ----
\* acceptors 1..9  =  a b c | d e f | g h i   (left/right/cross triangles)
CAcc == 1..9
CLrn == 1..4
CLQ == {{1,2,7,8},{1,3,7,9},{2,3,8,9}}
CRQ == {{4,5,7,8},{4,6,7,9},{5,6,8,9}}
CLG == {{1,2,3},{1,2,9},{1,8,3},{1,8,9},{7,2,3},{7,2,9},{7,8,3},{7,8,9}}
CRG == {{4,5,6},{4,5,9},{4,8,6},{4,8,9},{7,5,6},{7,5,9},{7,8,6},{7,8,9}}
CCG == {{7,8,9}}
CPairs == {{pr[1], pr[2]} : pr \in CLrn \X CLrn}
CQuorums == [l \in CLrn |-> IF l \in {1,2} THEN CLQ ELSE CRQ]
CSafety  == [p \in CPairs |-> IF p \subseteq {1,2} THEN CLG
                              ELSE IF p \subseteq {3,4} THEN CRG ELSE CCG]
CLGI == [learners |-> CLrn, acceptors |-> CAcc, safety_sets |-> CSafety, quorums |-> CQuorums]

\* ======================= general reduction lemmas =======================
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

\* ======================= concrete generator checks =======================
LEMMA VL_LL == \A m \in CLG : \A mx \in CLQ : \A my \in CLQ : (m \cap mx \cap my) # {}
  BY DEF CLG, CLQ
LEMMA VL_RR == \A m \in CRG : \A mx \in CRQ : \A my \in CRQ : (m \cap mx \cap my) # {}
  BY DEF CRG, CRQ
LEMMA VL_CX == \A m \in CCG : \A mx \in CLQ : \A my \in CRQ : (m \cap mx \cap my) # {}
  BY DEF CCG, CLQ, CRQ
LEMMA VL_XC == \A m \in CCG : \A mx \in CRQ : \A my \in CLQ : (m \cap mx \cap my) # {}
  BY DEF CCG, CRQ, CLQ
LEMMA C79L == {7,8,9} \in CLG BY DEF CLG
LEMMA C79R == {7,8,9} \in CRG BY DEF CRG
LEMMA CCGdef == CCG = {{7,8,9}} BY DEF CCG

\* ======================= resolution helpers =======================
LEMMA PairInCPairs == ASSUME NEW x \in 1..4, NEW y \in 1..4 PROVE {x,y} \in CPairs
  <1>1. <<x,y>> \in CLrn \X CLrn BY DEF CLrn
  <1>2. {x,y} = {<<x,y>>[1], <<x,y>>[2]} OBVIOUS
  <1> QED BY <1>1, <1>2 DEF CPairs

LEMMA Fields == ASSUME LearnerGraphInterface = CLGI
  PROVE /\ Learners = CLrn /\ Acceptors = CAcc
        /\ SpecifiedSafetySets = CSafety /\ SpecifiedQuorums = CQuorums
  BY DEF Learners, Acceptors, SpecifiedSafetySets, SpecifiedQuorums, CLGI

LEMMA SafetyResolve ==
  ASSUME LearnerGraphInterface = CLGI, NEW x \in 1..4, NEW y \in 1..4
  PROVE GetSpecifiedSafetySets({x,y}) =
        IF {x,y} \subseteq {1,2} THEN CLG ELSE IF {x,y} \subseteq {3,4} THEN CRG ELSE CCG
  <1>1. SpecifiedSafetySets = CSafety BY Fields
  <1>2. {x,y} \in CPairs BY PairInCPairs
  <1>3. {x,y} \in DOMAIN SpecifiedSafetySets BY <1>1, <1>2 DEF CSafety
  <1>4. GetSpecifiedSafetySets({x,y}) = CSafety[{x,y}] BY <1>1, <1>3 DEF GetSpecifiedSafetySets
  <1>5. CSafety[{x,y}] = IF {x,y} \subseteq {1,2} THEN CLG ELSE IF {x,y} \subseteq {3,4} THEN CRG ELSE CCG
    BY <1>2 DEF CSafety
  <1> QED BY <1>4, <1>5

LEMMA QuorumResolve ==
  ASSUME LearnerGraphInterface = CLGI, NEW x \in 1..4
  PROVE GetSpecifiedQuorums(x) = IF x \in {1,2} THEN CLQ ELSE CRQ
  <1>1. SpecifiedQuorums = CQuorums BY Fields
  <1>2. x \in DOMAIN SpecifiedQuorums BY <1>1 DEF CQuorums, CLrn
  <1>3. GetSpecifiedQuorums(x) = CQuorums[x] BY <1>1, <1>2 DEF GetSpecifiedQuorums
  <1>4. CQuorums[x] = IF x \in {1,2} THEN CLQ ELSE CRQ BY DEF CQuorums, CLrn
  <1> QED BY <1>3, <1>4

\* ======================= concrete Valid =======================
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

\* ======================= concrete Condensed =======================
LEMMA ConcreteCondensed ==
  ASSUME LearnerGraphInterface = CLGI
  PROVE \A x \in Learners : \A y \in Learners : \A z \in Learners :
          \A m1 \in GetSpecifiedSafetySets({x,y}) :
          \A m2 \in GetSpecifiedSafetySets({y,z}) :
            \E m3 \in GetSpecifiedSafetySets({x,z}) : m3 \subseteq (m1 \cup m2)
  <1>L. Learners = CLrn BY Fields
  <1> SUFFICES ASSUME NEW x \in Learners, NEW y \in Learners, NEW z \in Learners,
                      NEW m1 \in GetSpecifiedSafetySets({x,y}),
                      NEW m2 \in GetSpecifiedSafetySets({y,z})
               PROVE \E m3 \in GetSpecifiedSafetySets({x,z}) : m3 \subseteq (m1 \cup m2)
      OBVIOUS
  <1>1. x \in 1..4 /\ y \in 1..4 /\ z \in 1..4 BY <1>L DEF CLrn
  <1>xy. GetSpecifiedSafetySets({x,y}) = IF {x,y} \subseteq {1,2} THEN CLG ELSE IF {x,y} \subseteq {3,4} THEN CRG ELSE CCG
      BY <1>1, SafetyResolve
  <1>yz. GetSpecifiedSafetySets({y,z}) = IF {y,z} \subseteq {1,2} THEN CLG ELSE IF {y,z} \subseteq {3,4} THEN CRG ELSE CCG
      BY <1>1, SafetyResolve
  <1>xz. GetSpecifiedSafetySets({x,z}) = IF {x,z} \subseteq {1,2} THEN CLG ELSE IF {x,z} \subseteq {3,4} THEN CRG ELSE CCG
      BY <1>1, SafetyResolve
  <1>g. (x \in {1,2} \/ x \in {3,4}) /\ (y \in {1,2} \/ y \in {3,4}) /\ (z \in {1,2} \/ z \in {3,4}) BY <1>1
  <1>m1sub. m1 \subseteq (m1 \cup m2) OBVIOUS
  <1>m2sub. m2 \subseteq (m1 \cup m2) OBVIOUS
  <1>5. CASE x \in {1,2} /\ z \in {1,2}
    <2>xz. GetSpecifiedSafetySets({x,z}) = CLG BY <1>xz, <1>5
    <2>1. CASE y \in {1,2}
      <3>1. {x,y} \subseteq {1,2} BY <1>5, <2>1
      <3>2. m1 \in CLG BY <1>xy, <3>1
      <3> QED BY <3>2, <2>xz, <1>m1sub
    <2>2. CASE y \in {3,4}
      <3>1. ~({x,y} \subseteq {1,2}) /\ ~({x,y} \subseteq {3,4}) BY <1>5, <2>2
      <3>2. m1 \in CCG BY <1>xy, <3>1
      <3>3. m1 = {7,8,9} BY <3>2, CCGdef
      <3>4. {7,8,9} \in CLG BY C79L
      <3> QED BY <3>3, <3>4, <2>xz, <1>m1sub
    <2> QED BY <2>1, <2>2, <1>g
  <1>6. CASE x \in {3,4} /\ z \in {3,4}
    <2>xz. GetSpecifiedSafetySets({x,z}) = CRG
      <3>0. ~({x,z} \subseteq {1,2}) BY <1>6
      <3>1. {x,z} \subseteq {3,4} BY <1>6
      <3> QED BY <1>xz, <3>0, <3>1
    <2>1. CASE y \in {3,4}
      <3>0. ~({x,y} \subseteq {1,2}) BY <1>6, <2>1
      <3>1. {x,y} \subseteq {3,4} BY <1>6, <2>1
      <3>2. m1 \in CRG BY <1>xy, <3>0, <3>1
      <3> QED BY <3>2, <2>xz, <1>m1sub
    <2>2. CASE y \in {1,2}
      <3>1. ~({x,y} \subseteq {1,2}) /\ ~({x,y} \subseteq {3,4}) BY <1>6, <2>2
      <3>2. m1 \in CCG BY <1>xy, <3>1
      <3>3. m1 = {7,8,9} BY <3>2, CCGdef
      <3>4. {7,8,9} \in CRG BY C79R
      <3> QED BY <3>3, <3>4, <2>xz, <1>m1sub
    <2> QED BY <2>1, <2>2, <1>g
  <1>7. CASE x \in {1,2} /\ z \in {3,4}
    <2>xz. GetSpecifiedSafetySets({x,z}) = CCG
      <3>0. ~({x,z} \subseteq {1,2}) BY <1>7
      <3>1. ~({x,z} \subseteq {3,4}) BY <1>7
      <3> QED BY <1>xz, <3>0, <3>1
    <2>1. CASE y \in {1,2}
      <3>0. ~({y,z} \subseteq {1,2}) /\ ~({y,z} \subseteq {3,4}) BY <1>7, <2>1
      <3>1. m2 \in CCG BY <1>yz, <3>0
      <3>2. m2 = {7,8,9} BY <3>1, CCGdef
      <3>3. {7,8,9} \in CCG BY CCGdef
      <3> QED BY <3>2, <3>3, <2>xz, <1>m2sub
    <2>2. CASE y \in {3,4}
      <3>0. ~({x,y} \subseteq {1,2}) /\ ~({x,y} \subseteq {3,4}) BY <1>7, <2>2
      <3>1. m1 \in CCG BY <1>xy, <3>0
      <3>2. m1 = {7,8,9} BY <3>1, CCGdef
      <3>3. {7,8,9} \in CCG BY CCGdef
      <3> QED BY <3>2, <3>3, <2>xz, <1>m1sub
    <2> QED BY <2>1, <2>2, <1>g
  <1>8. CASE x \in {3,4} /\ z \in {1,2}
    <2>xz. GetSpecifiedSafetySets({x,z}) = CCG
      <3>0. ~({x,z} \subseteq {1,2}) BY <1>8
      <3>1. ~({x,z} \subseteq {3,4}) BY <1>8
      <3> QED BY <1>xz, <3>0, <3>1
    <2>1. CASE y \in {1,2}
      <3>0. ~({x,y} \subseteq {1,2}) /\ ~({x,y} \subseteq {3,4}) BY <1>8, <2>1
      <3>1. m1 \in CCG BY <1>xy, <3>0
      <3>2. m1 = {7,8,9} BY <3>1, CCGdef
      <3>3. {7,8,9} \in CCG BY CCGdef
      <3> QED BY <3>2, <3>3, <2>xz, <1>m1sub
    <2>2. CASE y \in {3,4}
      <3>0. ~({y,z} \subseteq {1,2}) /\ ~({y,z} \subseteq {3,4}) BY <1>8, <2>2
      <3>1. m2 \in CCG BY <1>yz, <3>0
      <3>2. m2 = {7,8,9} BY <3>1, CCGdef
      <3>3. {7,8,9} \in CCG BY CCGdef
      <3> QED BY <3>2, <3>3, <2>xz, <1>m2sub
    <2> QED BY <2>1, <2>2, <1>g
  <1> QED BY <1>5, <1>6, <1>7, <1>8, <1>g

\* ======================= type-OK =======================
LEMMA ConcreteSafetyType == ASSUME LearnerGraphInterface = CLGI PROVE SafetySetsTypeOK
  <1>1. SpecifiedSafetySets = CSafety /\ Acceptors = CAcc BY Fields
  <1>2. Learners = CLrn BY Fields
  <1>3. LearnerPairs = CPairs BY <1>2 DEF LearnerPairs, CPairs
  <1>4. \A p \in CPairs : CSafety[p] \in SUBSET (SUBSET CAcc)
    <2>1. CLG \in SUBSET (SUBSET CAcc) /\ CRG \in SUBSET (SUBSET CAcc) /\ CCG \in SUBSET (SUBSET CAcc)
      BY DEF CLG, CRG, CCG, CAcc
    <2> QED BY <2>1 DEF CSafety
  <1>5. CSafety \in [CPairs -> SUBSET (SUBSET CAcc)] BY <1>4 DEF CSafety
  <1> QED BY <1>1, <1>3, <1>5 DEF SafetySetsTypeOK

LEMMA ConcreteQuorumType == ASSUME LearnerGraphInterface = CLGI PROVE QuorumsTypeOK
  <1>1. SpecifiedQuorums = CQuorums /\ Acceptors = CAcc /\ Learners = CLrn BY Fields
  <1>2. \A l \in CLrn : CQuorums[l] \in SUBSET (SUBSET CAcc)
    <2>1. CLQ \in SUBSET (SUBSET CAcc) /\ CRQ \in SUBSET (SUBSET CAcc)
      BY DEF CLQ, CRQ, CAcc
    <2> QED BY <2>1 DEF CQuorums
  <1>3. CQuorums \in [CLrn -> SUBSET (SUBSET CAcc)] BY <1>2 DEF CQuorums
  <1> QED BY <1>1, <1>3 DEF QuorumsTypeOK

\* ======================= finiteness / non-emptiness =======================
LEMMA ConcreteFiniteAcceptors == ASSUME LearnerGraphInterface = CLGI PROVE FiniteAcceptors
  <1>1. Acceptors = CAcc BY Fields
  <1>2. IsFiniteSet(CAcc) BY FS_Interval DEF CAcc
  <1> QED BY <1>1, <1>2 DEF FiniteAcceptors

LEMMA ConcreteFiniteLearners == ASSUME LearnerGraphInterface = CLGI PROVE FiniteLearners
  <1>1. Learners = CLrn BY Fields
  <1>2. IsFiniteSet(CLrn) BY FS_Interval DEF CLrn
  <1> QED BY <1>1, <1>2 DEF FiniteLearners

LEMMA ConcreteLearnersNonEmpty == ASSUME LearnerGraphInterface = CLGI PROVE LearnersNonEmpty
  <1>1. Learners = CLrn BY Fields
  <1>2. CLrn # {} BY DEF CLrn
  <1> QED BY <1>1, <1>2 DEF LearnersNonEmpty

LEMMA ConcreteQuorumsNonEmpty == ASSUME LearnerGraphInterface = CLGI PROVE QuorumsNonEmpty
  <1>L. Learners = CLrn BY Fields
  <1> SUFFICES ASSUME NEW alpha \in Learners PROVE Quorums(alpha) # {}
    BY DEF QuorumsNonEmpty
  <1>1. alpha \in 1..4 BY <1>L DEF CLrn
  <1>2. GetSpecifiedQuorums(alpha) = IF alpha \in {1,2} THEN CLQ ELSE CRQ BY <1>1, QuorumResolve
  <1>3. GetSpecifiedQuorums(alpha) # {}
    <2>1. CLQ # {} BY DEF CLQ
    <2>2. CRQ # {} BY DEF CRQ
    <2> QED BY <1>2, <2>1, <2>2
  <1>4. PICK m \in GetSpecifiedQuorums(alpha) : TRUE BY <1>3
  <1>acc. Acceptors = CAcc BY Fields
  <1>5. m \subseteq Acceptors
    <2>1. m \subseteq CAcc BY <1>2, <1>4 DEF CLQ, CRQ, CAcc
    <2> QED BY <2>1, <1>acc
  <1>6. m \in SUBSET Acceptors BY <1>5
  <1>7. IsFiniteSet(Acceptors)
    <2>1. IsFiniteSet(CAcc) BY FS_Interval DEF CAcc
    <2> QED BY <1>acc, <2>1
  <1>8. m \in Quorums(alpha)
    <2>1. \E mm \in GetSpecifiedQuorums(alpha) : mm \subseteq m BY <1>4
    <2>2. IsFiniteSet(m) BY <1>5, <1>7, FS_Subset
    <2> QED BY <1>6, <2>1, <2>2 DEF Quorums
  <1> QED BY <1>8

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

\* ======================= main theorem =======================
THEOREM ConcreteSupportsAssumptions ==
  LearnerGraphInterface = CLGI => LearnerGraphAssumptions
  <1> SUFFICES ASSUME LearnerGraphInterface = CLGI PROVE LearnerGraphAssumptions OBVIOUS
  <1>1. SafetySetsTypeOK BY ConcreteSafetyType
  <1>2. QuorumsTypeOK BY ConcreteQuorumType
  <1>3. ValidLearnerGraphAssumption BY ValidReduction, ConcreteValid
  <1>4. Acceptors = CAcc BY Fields
  <1>5. IsFiniteSet(Acceptors) BY <1>4, FS_Interval DEF CAcc
  <1>6. CondensedLearnerGraphAssumption BY <1>5, CondensedReduction, ConcreteCondensed
  <1>7. FiniteAcceptors BY ConcreteFiniteAcceptors
  <1>8. FiniteLearners BY ConcreteFiniteLearners
  <1>9. LearnersNonEmpty BY ConcreteLearnersNonEmpty
  <1>10. QuorumsNonEmpty BY ConcreteQuorumsNonEmpty
  <1>11. LearnersMightAgree BY ConcreteLearnersMightAgree
  <1> QED BY <1>1, <1>2, <1>3, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11 DEF LearnerGraphAssumptions
=============================================================================
