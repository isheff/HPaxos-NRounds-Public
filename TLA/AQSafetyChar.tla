------------------------------ MODULE AQSafetyChar ------------------------------
\* Dictionary, safety side: under the embedding, membership in an edge's
\* safety sets is EXACTLY joint wisdom about the complement -- s is a safety
\* set of edge e iff every member of e foresees the failure of everyone
\* outside s.  In particular  SafeAcceptors \in SafetySets(e)  iff the
\* members of e are jointly wise about the actual faulty set.
EXTENDS AsymmetricQuorums, FiniteSetTheorems
LOCAL INSTANCE TLAPS

LEMMA AQSafetyChar ==
  ASSUME NEW fps, AQTypeOK(fps), AQEmbedded(fps), FiniteAcceptors,
         NEW e \in LearnerPairs, NEW s
  PROVE  s \in SafetySets(e) <=> (s \in SUBSET Acceptors /\ AQJointlyWise(fps, e, Acceptors \ s))
<1>gs. GetSpecifiedSafetySets(e) = {Acceptors \ f : f \in AQCommon(fps, e)}
  <2>1. SpecifiedSafetySets =
          [ee \in LearnerPairs |-> {Acceptors \ f : f \in AQCommon(fps, ee)}]
    BY DEF AQEmbedded
  <2> QED  BY <2>1 DEF GetSpecifiedSafetySets
<1>fwd. s \in SafetySets(e) => (s \in SUBSET Acceptors /\ AQJointlyWise(fps, e, Acceptors \ s))
  <2> SUFFICES ASSUME s \in SafetySets(e)
               PROVE  s \in SUBSET Acceptors /\ AQJointlyWise(fps, e, Acceptors \ s)
    OBVIOUS
  <2>sub. s \in SUBSET Acceptors  BY DEF SafetySets
  <2>m. PICK f \in AQCommon(fps, e) : (Acceptors \ f) \subseteq s  BY <1>gs DEF SafetySets
  <2>cw. (Acceptors \ s) \subseteq f
    <3> SUFFICES ASSUME NEW a \in Acceptors, a \notin s PROVE a \in f  OBVIOUS
    <3> QED  BY <2>m
  <2>jw. AQJointlyWise(fps, e, f)  BY <2>m DEF AQCommon
  <2> QED  BY <2>sub, <2>cw, <2>jw DEF AQJointlyWise, AQWise
<1>bwd. (s \in SUBSET Acceptors /\ AQJointlyWise(fps, e, Acceptors \ s)) => s \in SafetySets(e)
  <2> SUFFICES ASSUME s \in SUBSET Acceptors, AQJointlyWise(fps, e, Acceptors \ s)
               PROVE  s \in SafetySets(e)
    OBVIOUS
  <2>f. (Acceptors \ s) \in AQCommon(fps, e)  BY DEF AQCommon
  <2>m. (Acceptors \ (Acceptors \ s)) \subseteq s  OBVIOUS
  <2>fin. IsFiniteSet(s)  BY FS_Subset DEF FiniteAcceptors
  <2> QED  BY <2>f, <2>m, <2>fin, <1>gs DEF SafetySets
<1> QED  BY <1>fwd, <1>bwd
====================================================================
