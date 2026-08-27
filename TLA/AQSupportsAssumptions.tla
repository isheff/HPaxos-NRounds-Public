-------------------------- MODULE AQSupportsAssumptions --------------------------
\* The embedded learner graph of any B^3-satisfying asymmetric fail-prone
\* system satisfies ALL the learner-graph assumptions the HPaxos development
\* runs on.  Consequently every theorem of the development -- agreement,
\* termination, eventual knowledge, accountability -- applies to any
\* asymmetric quorum system, via the wisdom dictionary (AQSafetyChar,
\* AQQuorumChar).
EXTENDS AsymmetricQuorums, AQQuorumChar, AQSafetyChar, AQB3IffValid,
        FiniteSetTheorems
LOCAL INSTANCE TLAPS

THEOREM AQSupportsAssumptions ==
  ASSUME NEW fps, AQTypeOK(fps), AQNonTrivial(fps), AQB3(fps), AQEmbedded(fps),
         IsFiniteSet(Acceptors), Acceptors # {}
  PROVE  LearnerGraphAssumptions
<1>la. Learners = Acceptors  BY DEF AQEmbedded
<1>fa. FiniteAcceptors  BY DEF FiniteAcceptors
<1>lpsub. \A e \in LearnerPairs : e \subseteq Acceptors
  <2> SUFFICES ASSUME NEW e \in LearnerPairs PROVE e \subseteq Acceptors  OBVIOUS
  <2>1. PICK pr \in Learners \X Learners : e = {pr[1], pr[2]}  BY DEF LearnerPairs
  <2> QED  BY <2>1, <1>la
<1>c1. SafetySetsTypeOK
  <2>1. \A e \in LearnerPairs : {Acceptors \ f : f \in AQCommon(fps, e)} \in SUBSET SUBSET Acceptors
    OBVIOUS
  <2> QED  BY <2>1 DEF SafetySetsTypeOK, AQEmbedded
<1>c2. QuorumsTypeOK
  <2>1. \A i \in Acceptors : {Acceptors \ f : f \in fps[i]} \in SUBSET SUBSET Acceptors
    OBVIOUS
  <2> QED  BY <2>1, <1>la DEF QuorumsTypeOK, AQEmbedded
<1>c3. FiniteAcceptors  BY <1>fa
<1>c4. FiniteLearners  BY <1>fa, <1>la DEF FiniteLearners, FiniteAcceptors
<1>c5. LearnersNonEmpty  BY <1>la DEF LearnersNonEmpty
<1>c6. QuorumsNonEmpty
  <2> SUFFICES ASSUME NEW alpha \in Learners PROVE Quorums(alpha) # {}
    BY DEF QuorumsNonEmpty
  <2>aa. alpha \in Acceptors  BY <1>la
  <2>f. PICK f \in fps[alpha] : TRUE  BY <2>aa DEF AQNonTrivial
  <2>w. AQWise(fps, alpha, Acceptors \ Acceptors)
    <3>1. (Acceptors \ Acceptors) \subseteq f  OBVIOUS
    <3> QED  BY <3>1, <2>f DEF AQWise
  <2>q. Acceptors \in Quorums(alpha)  BY <2>aa, <2>w, <1>fa, AQQuorumChar
  <2> QED  BY <2>q
<1>c7. LearnersMightAgree
  <2> SUFFICES ASSUME NEW e \in LearnerPairs PROVE Acceptors \in SafetySets(e)
    BY DEF LearnersMightAgree
  <2>jw. AQJointlyWise(fps, e, Acceptors \ Acceptors)
    <3> SUFFICES ASSUME NEW i \in e PROVE AQWise(fps, i, Acceptors \ Acceptors)
      BY DEF AQJointlyWise
    <3>ia. i \in Acceptors  BY <1>lpsub
    <3>f. PICK f \in fps[i] : TRUE  BY <3>ia DEF AQNonTrivial
    <3>1. (Acceptors \ Acceptors) \subseteq f  OBVIOUS
    <3> QED  BY <3>1, <3>f DEF AQWise
  <2> QED  BY <2>jw, <1>fa, AQSafetyChar
<1>c8. CondensedLearnerGraphAssumption
  <2> SUFFICES ASSUME NEW x \in Learners, NEW y \in Learners, NEW z \in Learners,
                      NEW xy \in SafetySets({x, y}), NEW yz \in SafetySets({y, z})
               PROVE  (xy \cup yz) \in SafetySets({x, z})
    BY DEF CondensedLearnerGraphAssumption
  <2>lpxy. {x, y} \in LearnerPairs
    <3>1. <<x, y>> \in Learners \X Learners  OBVIOUS
    <3> QED  BY <3>1 DEF LearnerPairs
  <2>lpyz. {y, z} \in LearnerPairs
    <3>1. <<y, z>> \in Learners \X Learners  OBVIOUS
    <3> QED  BY <3>1 DEF LearnerPairs
  <2>lpxz. {x, z} \in LearnerPairs
    <3>1. <<x, z>> \in Learners \X Learners  OBVIOUS
    <3> QED  BY <3>1 DEF LearnerPairs
  <2>cxy. xy \in SUBSET Acceptors /\ AQJointlyWise(fps, {x, y}, Acceptors \ xy)
    BY <2>lpxy, <1>fa, AQSafetyChar
  <2>cyz. yz \in SUBSET Acceptors /\ AQJointlyWise(fps, {y, z}, Acceptors \ yz)
    BY <2>lpyz, <1>fa, AQSafetyChar
  <2>sub. (xy \cup yz) \in SUBSET Acceptors  BY <2>cxy, <2>cyz
  <2>jw. AQJointlyWise(fps, {x, z}, Acceptors \ (xy \cup yz))
    <3>wx. AQWise(fps, x, Acceptors \ (xy \cup yz))
      <4>1. AQWise(fps, x, Acceptors \ xy)  BY <2>cxy DEF AQJointlyWise
      <4>2. (Acceptors \ (xy \cup yz)) \subseteq (Acceptors \ xy)  OBVIOUS
      <4> QED  BY <4>1, <4>2 DEF AQWise
    <3>wz. AQWise(fps, z, Acceptors \ (xy \cup yz))
      <4>1. AQWise(fps, z, Acceptors \ yz)  BY <2>cyz DEF AQJointlyWise
      <4>2. (Acceptors \ (xy \cup yz)) \subseteq (Acceptors \ yz)  OBVIOUS
      <4> QED  BY <4>1, <4>2 DEF AQWise
    <3> QED  BY <3>wx, <3>wz DEF AQJointlyWise
  <2> QED  BY <2>lpxz, <2>sub, <2>jw, <1>fa, AQSafetyChar
<1>c9. ValidLearnerGraphAssumption  BY <1>fa, AQB3IffValid
<1> QED  BY <1>c1, <1>c2, <1>c3, <1>c4, <1>c5, <1>c6, <1>c7, <1>c8, <1>c9
  DEF LearnerGraphAssumptions
====================================================================
