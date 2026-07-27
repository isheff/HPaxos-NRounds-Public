--------------------------- MODULE ConcreteCondensed ---------------------------
EXTENDS LearnerGraphConcrete, Fields, SafetyResolve, CCGdef, C79L, C79R

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
=============================================================================
