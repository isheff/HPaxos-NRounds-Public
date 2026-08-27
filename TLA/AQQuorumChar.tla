------------------------------ MODULE AQQuorumChar ------------------------------
\* Dictionary, quorum side: under the embedding, membership in a learner's
\* quorum system is EXACTLY wisdom about the complement -- q is a quorum of i
\* iff i foresees the failure of everyone outside q.  (Canonical depth >= 1,
\* i.e. "has an all-correct quorum", coincides with wisdom.)
EXTENDS AsymmetricQuorums, FiniteSetTheorems
LOCAL INSTANCE TLAPS

LEMMA AQQuorumChar ==
  ASSUME NEW fps, AQTypeOK(fps), AQEmbedded(fps), FiniteAcceptors,
         NEW i \in Acceptors, NEW q
  PROVE  q \in Quorums(i) <=> (q \in SUBSET Acceptors /\ AQWise(fps, i, Acceptors \ q))
<1>gq. GetSpecifiedQuorums(i) = {Acceptors \ f : f \in fps[i]}
  <2>1. SpecifiedQuorums = [ii \in Acceptors |-> {Acceptors \ f : f \in fps[ii]}]
    BY DEF AQEmbedded
  <2> QED  BY <2>1 DEF GetSpecifiedQuorums
<1>fwd. q \in Quorums(i) => (q \in SUBSET Acceptors /\ AQWise(fps, i, Acceptors \ q))
  <2> SUFFICES ASSUME q \in Quorums(i)
               PROVE  q \in SUBSET Acceptors /\ AQWise(fps, i, Acceptors \ q)
    OBVIOUS
  <2>sub. q \in SUBSET Acceptors  BY DEF Quorums
  <2>m. PICK f \in fps[i] : (Acceptors \ f) \subseteq q  BY <1>gq DEF Quorums
  <2>cw. (Acceptors \ q) \subseteq f
    <3> SUFFICES ASSUME NEW a \in Acceptors, a \notin q PROVE a \in f  OBVIOUS
    <3> QED  BY <2>m
  <2> QED  BY <2>sub, <2>cw, <2>m DEF AQWise
<1>bwd. (q \in SUBSET Acceptors /\ AQWise(fps, i, Acceptors \ q)) => q \in Quorums(i)
  <2> SUFFICES ASSUME q \in SUBSET Acceptors, AQWise(fps, i, Acceptors \ q)
               PROVE  q \in Quorums(i)
    OBVIOUS
  <2>f. PICK f \in fps[i] : (Acceptors \ q) \subseteq f  BY DEF AQWise
  <2>m. (Acceptors \ f) \subseteq q
    <3> SUFFICES ASSUME NEW a \in Acceptors, a \notin f PROVE a \in q  OBVIOUS
    <3> QED  BY <2>f
  <2>fin. IsFiniteSet(q)  BY FS_Subset DEF FiniteAcceptors
  <2> QED  BY <2>f, <2>m, <2>fin, <1>gq DEF Quorums
<1> QED  BY <1>fwd, <1>bwd
====================================================================
