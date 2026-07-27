------------------------- MODULE TraceStepWitness -------------------------
EXTENDS MessageInterface,
        HasDepthDef, SafeQuorumsIntersectUncaught,
        UncaughtSameSigComparable, TranSubMessages, BMonotone, BBallot

\* The step-level analogue of SlowSupportWitness, at an arbitrary anchor
\* rlev in the chain. The two quorums intersect through g's
\* uncaught-as-of-rlev safety set; both members live in Tran(rlev), so the
\* uncaught common signer makes them Tran-comparable, and
\* B(ss) = lobal < B(mm) = B(rr) forces the direction ss \in Tran(rr).
LEMMA TraceStepWitness ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW alpha \in Learners, NEW g \in Learners,
         NEW lobal \in Ballots,
         NEW rlev \in Messages, NEW slev \in Messages, NEW mm \in Messages,
         NEW dep \in Nat, dep >= 1,
         g \in Con(alpha, rlev),
         g \in Lrns(mm),
         mm \in Tran(rlev),
         slev \in Tran(rlev),
         B(slev) = lobal,
         lobal < B(mm),
         HasDepth(alpha, slev, dep)
  PROVE \E rr \in Qd(g, mm, 1) : \E ss \in Qd(alpha, slev, dep) :
          Sig(rr) = Sig(ss) /\ ss \in Tran(rr)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lg. ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
<1>q1. SigS(Qd(g, mm, 1)) \in Quorums(g)
  <2>1. HasDepth(g, mm, 1)  BY DEF Lrns
  <2>2. 1 \in Nat /\ 1 # 0  OBVIOUS
  <2>3. HasDepth(g, mm, 1) =
          (/\ Sig(mm) \in Acceptors
           /\ IF 1 = 0 THEN (IsOneB(mm) /\ Fresh(g, mm))
                       ELSE SigS(Qd(g, mm, 1)) \in Quorums(g))
    BY <1>mi, <2>2, HasDepthDef
  <2> QED BY <2>1, <2>2, <2>3
<1>q2. SigS(Qd(alpha, slev, dep)) \in Quorums(alpha)
  <2>1. dep # 0  OBVIOUS
  <2>2. HasDepth(alpha, slev, dep) =
          (/\ Sig(slev) \in Acceptors
           /\ IF dep = 0 THEN (IsOneB(slev) /\ Fresh(alpha, slev))
                         ELSE SigS(Qd(alpha, slev, dep)) \in Quorums(alpha))
    BY <1>mi, HasDepthDef
  <2> QED BY <2>1, <2>2
<1>s. PICK s \in SafetySets({alpha, g}) : s \cap Caught(rlev) = {}
  BY DEF Con, ConFromCaught
<1>a. PICK a \in Acceptors :
        a \in SigS(Qd(alpha, slev, dep)) /\ a \in SigS(Qd(g, mm, 1)) /\ a \notin Caught(rlev)
  BY <1>lg, <1>s, <1>q1, <1>q2, SafeQuorumsIntersectUncaught
<1>ss. PICK ss \in Qd(alpha, slev, dep) : a = Sig(ss)  BY <1>a DEF SigS
<1>rr. PICK rr \in Qd(g, mm, 1) : a = Sig(rr)  BY <1>a DEF SigS
<1>ssP. ss \in TranExclusive(slev) /\ B(ss) = B(slev)
  <2>1. ss \in TranExclusive(slev) /\ B(slev) = B(ss)  BY <1>ss, <1>mi DEF Qd
  <2> QED BY <2>1
<1>rrP. rr \in TranExclusive(mm) /\ B(rr) = B(mm)
  <2>1. rr \in TranExclusive(mm) /\ B(mm) = B(rr)  BY <1>rr, <1>mi DEF Qd
  <2> QED BY <2>1
<1>ssT. ss \in Tran(rlev)
  <2>1. ss \in Tran(slev)  BY <1>ssP DEF TranExclusive
  <2>2. Tran(slev) \subseteq Tran(rlev)  BY <1>mi DEF TranTrans
  <2> QED BY <2>1, <2>2
<1>rrT. rr \in Tran(rlev)
  <2>1. rr \in Tran(mm)  BY <1>rrP DEF TranExclusive
  <2>2. Tran(mm) \subseteq Tran(rlev)  BY <1>mi DEF TranTrans
  <2> QED BY <2>1, <2>2
<1>cmp. ss \in Tran(rr) \/ rr \in Tran(ss)
  <2>1. a \notin CaughtS(Tran(rlev))  BY <1>a DEF Caught
  <2> QED BY <2>1, <1>ssT, <1>rrT, <1>ss, <1>rr, UncaughtSameSigComparable
<1>ssM. ss \in Messages
  <2>1. Tran(rlev) \subseteq Messages  BY <1>mi, TranSubMessages
  <2> QED BY <1>ssT, <2>1
<1>bmm. B(mm) \in Ballots  BY <1>mi, BBallot
<1>notrev. rr \notin Tran(ss)
  <2> SUFFICES ASSUME rr \in Tran(ss) PROVE FALSE  OBVIOUS
  <2>1. B(rr) <= B(ss)  BY <1>mi, <1>ssM, BMonotone
  <2>2. B(rr) = B(mm)  BY <1>rrP
  <2>3. B(ss) = lobal  BY <1>ssP
  <2>4. B(mm) \in Nat /\ lobal \in Nat  BY <1>bmm DEF Ballots
  <2> QED BY <2>1, <2>2, <2>3, <2>4
<1>dir. ss \in Tran(rr)  BY <1>cmp, <1>notrev
<1>sig. Sig(rr) = Sig(ss)  BY <1>rr, <1>ss
<1> QED BY <1>rr, <1>ss, <1>sig, <1>dir
====================================================================
