------------------------ MODULE SlowSupportWitness ------------------------
EXTENDS MessageInterface,
        TranClosureClosed, HasDepthDef, SafeQuorumsIntersectUncaught,
        UncaughtSameSigComparable, BMonotone, BBallot

\* Given any valid (g,m) pairing, produces a matching (rr,ss) pair. The two
\* quorums intersect (SafeQuorumsIntersectUncaught) in an uncaught acceptor
\* signing both; same signer + uncaught makes them Tran-comparable
\* (UncaughtSameSigComparable), and B(r0)=B(m)>lobal=B(s0) forces the
\* direction via BMonotone.
LEMMA SlowSupportWitness ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW lobal \in Ballots,
         DecisionSlow(mset, alpha, lobal),
         NEW g \in Learners, g \in ConFromCaught(alpha, CaughtS(TranClosure(mset))),
         NEW m \in TranClosure(mset), g \in Lrns(m), lobal < B(m)
  PROVE \E rr \in Qd(g, m, 1) : \E ss \in Tran(rr) :
          /\ Sig(rr) = Sig(ss)
          /\ B(ss) = lobal
          /\ HasDepth(alpha, ss, MaxDepth(alpha))
<1> DEFINE W == {x \in TranClosure(mset) : B(x) = lobal /\ HasDepth(alpha, x, MaxDepth(alpha))}
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lgv. ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
<1>mM. m \in Messages  BY <1>mi, TranClosureClosed
<1>sigW. SigS(W) \in Quorums(alpha)  BY DEF DecisionSlow
<1>lrn. HasDepth(g, m, 1)  BY DEF Lrns
<1>hd1. Sig(m) \in Acceptors /\ SigS(Qd(g, m, 1)) \in Quorums(g)
  <2>1. 1 \in Nat /\ 1 # 0  OBVIOUS
  <2>2. HasDepth(g, m, 1) =
          (/\ Sig(m) \in Acceptors
           /\ IF 1 = 0 THEN (IsOneB(m) /\ Fresh(g, m))
                       ELSE SigS(Qd(g, m, 1)) \in Quorums(g))
    BY <1>mi, <1>mM, <2>1, HasDepthDef
  <2> QED BY <1>lrn, <2>1, <2>2
<1>q2. SigS(Qd(g, m, 1)) \in Quorums(g)  BY <1>hd1
<1>con. PICK s \in SafetySets({alpha, g}) : s \cap CaughtS(TranClosure(mset)) = {}  BY DEF ConFromCaught
<1>inter. \E a \in Acceptors : a \in SigS(W) /\ a \in SigS(Qd(g,m,1)) /\ a \notin CaughtS(TranClosure(mset))
  BY <1>con, <1>sigW, <1>q2, <1>lgv, SafeQuorumsIntersectUncaught
<1> PICK a \in Acceptors : a \in SigS(W) /\ a \in SigS(Qd(g,m,1)) /\ a \notin CaughtS(TranClosure(mset))
  BY <1>inter
<1>s0. PICK s0 \in W : a = Sig(s0)  BY DEF SigS
<1>r0. PICK r0 \in Qd(g,m,1) : a = Sig(r0)  BY DEF SigS
<1>s0M. s0 \in TranClosure(mset) /\ B(s0) = lobal /\ HasDepth(alpha, s0, MaxDepth(alpha))  BY <1>s0
<1>r0Q. r0 \in TranExclusive(m) /\ B(m) = B(r0)  BY <1>r0 DEF Qd
<1>r0B. B(r0) = B(m)  BY <1>r0Q
<1>s0inCL. s0 \in TranClosure(mset)  BY <1>s0M
<1>r0inCL. r0 \in TranClosure(mset)
  <2>1. r0 \in Tran(m)  BY <1>r0Q DEF TranExclusive
  <2>2. m \in Messages /\ Tran(m) \subseteq TranClosure(mset)  BY <1>mi, TranClosureClosed
  <2> QED BY <2>1, <2>2
<1>cmp. s0 \in Tran(r0) \/ r0 \in Tran(s0)
  BY <1>s0inCL, <1>r0inCL, UncaughtSameSigComparable, <1>s0, <1>r0
<1>notRev. r0 \notin Tran(s0)
  <2> SUFFICES ASSUME r0 \in Tran(s0) PROVE FALSE  OBVIOUS
  <2>1. s0 \in Messages  BY <1>s0inCL, <1>mi, TranClosureClosed
  <2>2. B(r0) <= B(s0)  BY <2>1, <1>mi, BMonotone
  <2>3. B(r0) = B(m)  BY <1>r0B
  <2>4. B(s0) = lobal  BY <1>s0M
  <2>5. B(m) \in Nat /\ lobal \in Nat
    <3>1. B(m) \in Ballots  BY <1>mi, <1>mM, BBallot
    <3> QED BY <3>1 DEF Ballots
  <2> QED BY <2>2, <2>3, <2>4, <2>5
<1>ss0Tran. s0 \in Tran(r0)  BY <1>cmp, <1>notRev
<1>sigeq. Sig(r0) = Sig(s0)  BY <1>r0, <1>s0
<1> QED BY <1>r0, <1>ss0Tran, <1>sigeq, <1>s0M
====================================================================
