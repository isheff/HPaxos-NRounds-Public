---------------------------- MODULE TriangleWiseServed ----------------------------
\* The separation witness, protocol side: run authenticated HPaxos over the
\* EMBEDDED triangle.  In the Lemma-4.4 scenario where pc is faulty (the
\* other two scenarios are literally symmetric under rotating pa,pb,pc), the
\* wise depth-one acceptor pa -- as a learner -- gets full consensus:
\* termination at its live canonical quorum {pa, pb}.  Meanwhile
\* NoSymmetricQuorumF1 shows NO symmetric quorum system tolerates all the
\* scenarios of TriF1.  Unauthenticated, consensus for depth-one processes is
\* impossible (Amores-Sesar et al., OPODIS 2025); with authentication, one
\* fixed configuration serves the wise process of every TriF1 scenario.
EXTENDS HPaxosPlusCal, AsymmetricTriangle, TriangleB3, TriangleWise,
        AsymmetricTermination, TerminationAt, FiniteSetTheorems
LOCAL INSTANCE TLAPS

THEOREM TriangleWiseServed ==
  ASSUME MessageInterfaceAssumptions, ValueInterfaceAssumptions, AcceptorsAssumptions,
         NEW pa, NEW pb, NEW pc, pa # pb, pb # pc, pa # pc,
         Acceptors = {pa, pb, pc},
         AQEmbedded(TriFPS(pa, pb, pc)),
         Spec, NetworkAssumption,
         \* the pc-faulty scenario: pa and pb are the safe acceptors, and
         \* both are fair, so pa's canonical quorum {pa, pb} is live
         SafeAcceptors = {pa, pb}, LiveAcceptors = {pa, pb},
         NEW bal \in Ballots
  PROVE  \E p \in Proposals :
           (( /\ \A x \in Proposals : (((<>KnownToLive(x)) /\ (B(x) > bal)) => (x = p))
              /\ <>(p \in Msgs)
              /\ TranFairness(p)
           ) => <> Decision(Msgs, pa, B(p)))
<1>fin. IsFiniteSet(Acceptors)
  <2>1. IsFiniteSet({pa})  BY FS_Singleton
  <2>2. IsFiniteSet({pa} \cup {pb})  BY <2>1, FS_AddElement
  <2>3. IsFiniteSet(({pa} \cup {pb}) \cup {pc})  BY <2>2, FS_AddElement
  <2>4. Acceptors = ({pa} \cup {pb}) \cup {pc}  OBVIOUS
  <2> QED  BY <2>3, <2>4
<1>ne. Acceptors # {}  OBVIOUS
\* fps appears only in AsymmetricTermination's hypotheses, never its
\* conclusion: bind the compound TriFPS(..) to a fresh variable first, so
\* the application matches an already-bound identifier instead of
\* blind-searching a witness (hidden-parameter gotcha).
<1>fps. PICK fpsv \in {TriFPS(pa, pb, pc)} : TRUE  OBVIOUS
<1>feq. fpsv = TriFPS(pa, pb, pc)  BY <1>fps
<1>wf0. /\ AQTypeOK(TriFPS(pa, pb, pc))
        /\ AQNonTrivial(TriFPS(pa, pb, pc))
        /\ AQB3(TriFPS(pa, pb, pc))
  BY TriangleB3
<1>ty. AQTypeOK(fpsv)  BY <1>wf0, <1>feq
<1>nt. AQNonTrivial(fpsv)  BY <1>wf0, <1>feq
<1>b3. AQB3(fpsv)  BY <1>wf0, <1>feq
<1>emb. AQEmbedded(fpsv)  BY <1>feq
<1>al. pa \in Learners  BY DEF AQEmbedded
<1>cmp. Acceptors \ LiveAcceptors = {pc} /\ Acceptors \ SafeAcceptors = {pc}
  OBVIOUS
<1>w. AQWise(TriFPS(pa, pb, pc), pa, {pc})  BY TriangleWise
<1>wv. AQWise(fpsv, pa, {pc})  BY <1>w, <1>feq
<1>wl. AQWise(fpsv, pa, Acceptors \ LiveAcceptors)
  BY <1>wv, <1>cmp
<1>ws. AQWise(fpsv, pa, Acceptors \ SafeAcceptors)
  BY <1>wv, <1>cmp
\* inline AsymmetricTermination's own derivation (its citation as a single
\* fact exhausts the backend in this heavier context)
<1>lga. LearnerGraphAssumptions
  BY <1>ty, <1>nt, <1>b3, <1>emb, <1>fin, <1>ne, AQSupportsAssumptions
<1>fa2. FiniteAcceptors  BY <1>fin DEF FiniteAcceptors
<1>aa. pa \in Acceptors  OBVIOUS
<1>lsub. LiveAcceptors \in SUBSET Acceptors
  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption, LiveAcceptorsAssumption
<1>ssub. SafeAcceptors \in SUBSET Acceptors
  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption
<1>lq. LiveAcceptors \in Quorums(pa)
  BY <1>aa, <1>lsub, <1>wl, <1>fa2, <1>emb, <1>ty, AQQuorumChar
<1>lp. {pa} \in LearnerPairs
  <2>1. <<pa, pa>> \in Learners \X Learners  BY <1>al
  <2>2. {pa, pa} \in LearnerPairs  BY <2>1 DEF LearnerPairs
  <2> QED  BY <2>2
<1>jw. AQJointlyWise(fpsv, {pa}, Acceptors \ SafeAcceptors)
  BY <1>ws DEF AQJointlyWise
<1>ss. SafeAcceptors \in SafetySets({pa})
  BY <1>lp, <1>ssub, <1>jw, <1>fa2, <1>emb, <1>ty, AQSafetyChar
<1>op. TermAtOp(pa, bal)  BY <1>lga, <1>al, <1>lq, <1>ss, TerminationAt
<1> QED  BY <1>op DEF TermAtOp
====================================================================
