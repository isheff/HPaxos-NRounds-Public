------------------------------ MODULE AQB3IffValid ------------------------------
\* The embedding theorem: the B^3 condition on an asymmetric fail-prone
\* system is EQUIVALENT to the validity of the embedded condensed learner
\* graph.  The two conditions are complements of each other:
\*     s \cap qx \cap qy  =  Acceptors \ (fi \cup fj \cup fij).
EXTENDS AsymmetricQuorums, AQQuorumChar, AQSafetyChar
LOCAL INSTANCE TLAPS

LEMMA AQB3IffValid ==
  ASSUME NEW fps, AQTypeOK(fps), AQEmbedded(fps), FiniteAcceptors
  PROVE  AQB3(fps) <=> ValidLearnerGraphAssumption
<1>la. Learners = Acceptors  BY DEF AQEmbedded
<1>fwd. AQB3(fps) => ValidLearnerGraphAssumption
  <2> SUFFICES ASSUME AQB3(fps),
                      NEW x \in Learners, NEW y \in Learners,
                      NEW s \in SafetySets({x, y}),
                      NEW qx \in Quorums(x), NEW qy \in Quorums(y)
               PROVE  (s \cap qx \cap qy) # {}
    BY DEF ValidLearnerGraphAssumption
  <2>xa. x \in Acceptors /\ y \in Acceptors  BY <1>la
  <2>lp. {x, y} \in LearnerPairs
    <3>1. <<x, y>> \in Learners \X Learners  OBVIOUS
    <3> QED  BY <3>1 DEF LearnerPairs
  <2>schar. s \in SUBSET Acceptors /\ AQJointlyWise(fps, {x, y}, Acceptors \ s)
    BY <2>lp, AQSafetyChar
  <2>scom. (Acceptors \ s) \in AQCommon(fps, {x, y})
    BY <2>schar DEF AQCommon
  <2>qxw. AQWise(fps, x, Acceptors \ qx)  BY <2>xa, AQQuorumChar
  <2>qyw. AQWise(fps, y, Acceptors \ qy)  BY <2>xa, AQQuorumChar
  <2>fx. PICK fx \in fps[x] : (Acceptors \ qx) \subseteq fx  BY <2>qxw DEF AQWise
  <2>fy. PICK fy \in fps[y] : (Acceptors \ qy) \subseteq fy  BY <2>qyw DEF AQWise
  <2>a. PICK a \in Acceptors : a \notin fx /\ a \notin fy /\ a \notin (Acceptors \ s)
    BY <2>fx, <2>fy, <2>scom, <2>xa DEF AQB3
  <2>aqx. a \in qx  BY <2>a, <2>fx
  <2>aqy. a \in qy  BY <2>a, <2>fy
  <2>as. a \in s  BY <2>a
  <2> QED  BY <2>aqx, <2>aqy, <2>as
<1>bwd. ValidLearnerGraphAssumption => AQB3(fps)
  <2> SUFFICES ASSUME ValidLearnerGraphAssumption,
                      NEW i \in Acceptors, NEW j \in Acceptors,
                      NEW fi \in fps[i], NEW fj \in fps[j],
                      NEW fij \in AQCommon(fps, {i, j})
               PROVE  \E a \in Acceptors : a \notin fi /\ a \notin fj /\ a \notin fij
    BY DEF AQB3
  <2>il. i \in Learners /\ j \in Learners  BY <1>la
  <2>lp. {i, j} \in LearnerPairs
    <3>1. <<i, j>> \in Learners \X Learners  BY <2>il
    <3> QED  BY <3>1 DEF LearnerPairs
  <2>ft. fi \in SUBSET Acceptors /\ fj \in SUBSET Acceptors  BY DEF AQTypeOK
  <2>qx. (Acceptors \ fi) \in Quorums(i)
    <3>w. AQWise(fps, i, Acceptors \ (Acceptors \ fi))
      <4>1. (Acceptors \ (Acceptors \ fi)) \subseteq fi  OBVIOUS
      <4> QED  BY <4>1 DEF AQWise
    <3> QED  BY <3>w, AQQuorumChar
  <2>qy. (Acceptors \ fj) \in Quorums(j)
    <3>w. AQWise(fps, j, Acceptors \ (Acceptors \ fj))
      <4>1. (Acceptors \ (Acceptors \ fj)) \subseteq fj  OBVIOUS
      <4> QED  BY <4>1 DEF AQWise
    <3> QED  BY <3>w, AQQuorumChar
  <2>s. (Acceptors \ fij) \in SafetySets({i, j})
    <3>jw0. AQJointlyWise(fps, {i, j}, fij)  BY DEF AQCommon
    <3>sub. (Acceptors \ (Acceptors \ fij)) \subseteq fij  OBVIOUS
    <3>jw. AQJointlyWise(fps, {i, j}, Acceptors \ (Acceptors \ fij))
      BY <3>jw0, <3>sub DEF AQJointlyWise, AQWise
    <3> QED  BY <3>jw, <2>lp, AQSafetyChar
  <2>val. ((Acceptors \ fij) \cap (Acceptors \ fi) \cap (Acceptors \ fj)) # {}
    BY <2>il, <2>s, <2>qx, <2>qy DEF ValidLearnerGraphAssumption
  <2>a. PICK a \in (Acceptors \ fij) \cap (Acceptors \ fi) \cap (Acceptors \ fj) : TRUE
    BY <2>val
  <2> QED  BY <2>a
<1> QED  BY <1>fwd, <1>bwd
====================================================================
