------------------------ MODULE TraceContradiction ------------------------
\* SequenceTheorems supplies SeqDef and LenProperties. It was dropped from
\* MessageInterface's header as proof-only; this is the one lemma that needs
\* it, so it is pulled in here rather than re-added to the interface.
EXTENDS MessageInterface, SequenceTheorems,
        MaxDepthFiniteAcceptors, TraceCoreProperties,
        TranClosureClosed, TranCardNat,
        ConFromCaughtAllCaught, CaughtSubClosure, CaughtMonotoneTran,
        ValidSeqsLenMaxDepth

\* A full-length minimal trace is impossible: prepending Acceptors (whose
\* ConFromCaught is empty) and CaughtS(closure) (whose ConFromCaught
\* contains beta but, by minimality of B(seq[1].mm), NOT seq[2].gamma) to
\* the shrinking caught sets Caught(seq[x].rr) yields a ValidSeqs(alpha)
\* chain of length MaxDepth(alpha) + 2, contradicting ValidSeqsLenMaxDepth.
LEMMA TraceContradiction ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         NEW lobal \in Ballots,
         NEW himsg \in TranClosure(mset),
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset))),
         NEW seq \in [1..MaxDepth(alpha)+1 -> TraceElem],
         \A x \in 1..MaxDepth(alpha)+1 :
           TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
  PROVE FALSE
<1> DEFINE K == MaxDepth(alpha) + 1
<1> DEFINE CL == TranClosure(mset)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lg. FiniteAcceptors /\ FiniteLearners /\ LearnersNonEmpty /\ QuorumsNonEmpty
       /\ LearnersMightAgree /\ CondensedLearnerGraphAssumption /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>Kge2. K >= 2 /\ K \in Nat /\ MaxDepth(alpha) \in Nat
  <2>1. MaxDepth(alpha) \in 1..Cardinality(Acceptors)  BY <1>lg, MaxDepthFiniteAcceptors
  <2> QED BY <2>1
<1> USE <1>Kge2
<1>core. \A x \in 1..K : TraceCondCore(alpha, lobal, CL, himsg, seq, x)
  <2> SUFFICES ASSUME NEW x \in 1..K PROVE TraceCondCore(alpha, lobal, CL, himsg, seq, x)  OBVIOUS
  <2> QED BY DEF TraceCondCoreMin
<1>tcp. /\ \A i \in 1..K : /\ seq[i].mm \in CL /\ seq[i].rr \in CL /\ seq[i].ss \in CL
        /\ \A i, j \in 1..K : i < j => seq[j].rr \in Tran(seq[i].rr)
        /\ \A i, j \in 1..K : (i < j /\ j < K) =>
             /\ Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr)
             /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
  BY <1>core, <1>Kge2, TraceCoreProperties
<1>tcpA. \A i \in 1..K : seq[i].mm \in CL /\ seq[i].rr \in CL /\ seq[i].ss \in CL  BY <1>tcp
<1>tcpB. \A i, j \in 1..K : i < j => seq[j].rr \in Tran(seq[i].rr)  BY <1>tcp
<1>tcpC. \A i, j \in 1..K : (i < j /\ j < K) =>
             Con(alpha, seq[i].rr) \subseteq Con(alpha, seq[j].rr) /\ Con(alpha, seq[i].rr) # Con(alpha, seq[j].rr)
  BY <1>tcp
\* seq[2].gamma is NOT connected given only CaughtS(closure): otherwise the
\* record z below (= seq[2], relabelled to index 1) would be a valid <1>
\* candidate with a strictly lower Cardinality(Tran(.)) than seq[1].mm,
\* contradicting seq[1]'s minimality (TraceCondCoreMin).
<1>notin2. seq[2].gamma \notin ConFromCaught(alpha, CaughtS(CL))
  <2> SUFFICES ASSUME seq[2].gamma \in ConFromCaught(alpha, CaughtS(CL)) PROVE FALSE  OBVIOUS
  <2>1dom. 1 \in 1..K  BY <1>Kge2
  <2>2dom. 2 \in 1..K  BY <1>Kge2
  <2>min1. TraceCondCoreMin(alpha, lobal, CL, himsg, seq, 1)  BY <2>1dom
  <2>c2. TraceCondCore(alpha, lobal, CL, himsg, seq, 2)  BY <2>2dom DEF TraceCondCoreMin
  <2> DEFINE z == [mm |-> seq[2].mm, rr |-> seq[2].rr, ss |-> seq[2].ss, gamma |-> seq[2].gamma]
  <2>zType. z \in TraceElem
    <3>1. seq[2].mm \in Messages /\ seq[2].rr \in Messages /\ seq[2].ss \in Messages /\ seq[2].gamma \in Learners
      <4>inCL. seq[2].mm \in CL /\ seq[2].rr \in CL /\ seq[2].ss \in CL  BY <1>tcpA, <2>2dom
      <4>clsub. CL \subseteq Messages
        <5> SUFFICES ASSUME NEW y \in CL PROVE y \in Messages  OBVIOUS
        <5> QED BY <1>mi, TranClosureClosed
      <4>gam. seq[2].gamma \in Learners  BY <2>c2 DEF TraceCondCore, Lrns
      <4> QED BY <4>inCL, <4>clsub, <4>gam
    <3> QED BY <3>1 DEF TraceElem
  <2>zmm. z.mm = seq[2].mm  OBVIOUS
  <2>i1. TraceCondCore(alpha, lobal, CL, himsg, [seq EXCEPT ![1] = z], 1)
    <3> DEFINE seq2 == [seq EXCEPT ![1] = z]
    <3>s1. seq2[1] = z  BY <1>Kge2
    <3>c1. /\ z.mm \in Tran(himsg)
           /\ lobal < B(z.mm)
           /\ z.gamma \in Lrns(z.mm)
           /\ z.rr \in Qd(z.gamma, z.mm, 1)
           /\ z.ss \in Tran(z.rr)
           /\ Sig(z.rr) = Sig(z.ss)
           /\ B(z.ss) = lobal
           /\ V(z.mm) = V(himsg)
      BY <2>c2 DEF TraceCondCore
    <3>c1a. z.gamma \in ConFromCaught(alpha, CaughtS(CL))  OBVIOUS
    <3> QED BY <3>s1, <3>c1, <3>c1a DEF TraceCondCore
  <2>minapp. Cardinality(Tran(seq[1].mm)) <= Cardinality(Tran(z.mm))
    BY <2>min1, <2>zType, <2>i1 DEF TraceCondCoreMin
  <2>lt. Cardinality(Tran(seq[2].mm)) < Cardinality(Tran(seq[1].mm))
    <3>1. 2 > 1 /\ 2 - 1 = 1  OBVIOUS
    <3> QED BY <2>c2, <3>1 DEF TraceCondCore
  <2>ty. Cardinality(Tran(seq[1].mm)) \in Nat /\ Cardinality(Tran(seq[2].mm)) \in Nat
    <3>1. seq[1].mm \in CL /\ seq[2].mm \in CL  BY <1>tcpA, <2>1dom, <2>2dom
    <3>2. seq[1].mm \in Messages /\ seq[2].mm \in Messages  BY <3>1, <1>mi, TranClosureClosed
    <3> QED BY <3>2, <1>mi, TranCardNat
  <2> QED BY <2>minapp, <2>zmm, <2>lt, <2>ty
\* the chain: Acceptors, CaughtS(closure), Caught(seq[1].rr), .., Caught(seq[K-1].rr)
<1> DEFINE l == [i \in 1..(K+1) |->
      IF i = 1 THEN Acceptors
      ELSE IF i = 2 THEN CaughtS(CL)
      ELSE Caught(seq[i-2].rr)]
<1>lrange. \A i \in 1..(K+1) : l[i] \subseteq Acceptors
  <2> SUFFICES ASSUME NEW i \in 1..(K+1) PROVE l[i] \subseteq Acceptors  OBVIOUS
  <2>1. CASE i = 1  BY <2>1
  <2>2. CASE i = 2  BY <2>2 DEF CaughtS
  <2>3. CASE i \notin {1,2}
    <3>1. l[i] = Caught(seq[i-2].rr)  BY <2>3
    <3> QED BY <3>1 DEF Caught, CaughtS
  <2> QED BY <2>1, <2>2, <2>3
<1>lfun. l \in [1..(K+1) -> SUBSET Acceptors]  BY <1>lrange
<1>lseq. l \in Seq(SUBSET Acceptors)
  <2>1. K + 1 \in Nat  BY <1>Kge2
  <2> QED BY <1>lfun, <2>1, SeqDef
<1>llen. Len(l) = K + 1
  <2>props. Len(l) \in Nat /\ DOMAIN l = 1..Len(l)  BY <1>lseq, LenProperties
  <2>dom. DOMAIN l = 1..(K+1)  OBVIOUS
  <2>eq. 1..Len(l) = 1..(K+1)  BY <2>props, <2>dom
  <2>in1. K + 1 \in 1..(K+1)  BY <1>Kge2
  <2>le1. K + 1 <= Len(l)
    <3>1. K + 1 \in 1..Len(l)  BY <2>eq, <2>in1
    <3> QED BY <3>1, <2>props
  <2>le2. Len(l) <= K + 1
    <3>1. Len(l) \in 1..Len(l)  BY <2>props, <2>le1, <1>Kge2
    <3>2. Len(l) \in 1..(K+1)  BY <3>1, <2>eq
    <3> QED BY <3>2
  <2> QED BY <2>le1, <2>le2, <2>props, <1>Kge2
<1>trans. \A i \in 1..K : l[i+1] \subseteq l[i] /\ ConFromCaught(alpha, l[i]) # ConFromCaught(alpha, l[i+1])
  <2> SUFFICES ASSUME NEW i \in 1..K
               PROVE l[i+1] \subseteq l[i] /\ ConFromCaught(alpha, l[i]) # ConFromCaught(alpha, l[i+1])
    OBVIOUS
  <2>a. CASE i = 1
    <3>l1. l[1] = Acceptors  BY <2>a
    <3>l2. l[2] = CaughtS(CL)  BY <2>a
    <3>sub. l[2] \subseteq l[1]  BY <3>l1, <3>l2 DEF CaughtS
    <3>con1. ConFromCaught(alpha, Acceptors) = {}  BY <1>lg, ConFromCaughtAllCaught
    <3>betaIn. beta \in ConFromCaught(alpha, CaughtS(CL))  OBVIOUS
    <3>ne2. ConFromCaught(alpha, CaughtS(CL)) # {}  BY <3>betaIn
    <3>diff. ConFromCaught(alpha, l[1]) # ConFromCaught(alpha, l[2])  BY <3>l1, <3>l2, <3>con1, <3>ne2
    <3> QED BY <3>sub, <3>diff, <2>a
  <2>b. CASE i = 2
    <3>l2. l[2] = CaughtS(CL)  BY <2>b
    <3>l3. l[3] = Caught(seq[1].rr)  BY <2>b
    <3>rTC. seq[1].rr \in CL
      <4>1dom. 1 \in 1..K  BY <1>Kge2
      <4> QED BY <4>1dom, <1>tcpA
    <3>sub. l[3] \subseteq l[2]  BY <3>l3, <3>l2, <3>rTC, <1>mi, CaughtSubClosure
    <3>betaIn. beta \in ConFromCaught(alpha, l[2])  BY <3>l2
    <3>notin. seq[2].gamma \notin ConFromCaught(alpha, l[2])  BY <3>l2, <1>notin2
    <3>2dom. 2 \in 1..K  BY <1>Kge2
    <3>c2. TraceCondCore(alpha, lobal, CL, himsg, seq, 2)  BY <3>2dom DEF TraceCondCoreMin
    <3>g5in. seq[2].gamma \in Con(alpha, seq[1].rr)
      <4>1. 2 > 1  OBVIOUS
      <4> QED BY <3>c2, <4>1 DEF TraceCondCore
    <3>g5in2. seq[2].gamma \in ConFromCaught(alpha, l[3])  BY <3>g5in, <3>l3 DEF Con
    <3>diff. ConFromCaught(alpha, l[2]) # ConFromCaught(alpha, l[3])  BY <3>notin, <3>g5in2
    <3> QED BY <3>sub, <3>diff, <2>b
  <2>c. CASE i \notin {1,2}
    <3>x. i - 2 \in 1..(K-1)  BY <2>c
    <3>li. l[i] = Caught(seq[i-2].rr)  BY <2>c
    <3>eqidx. (i+1) - 2 = (i - 2) + 1  OBVIOUS
    <3>li1. l[i+1] = Caught(seq[(i-2)+1].rr)  BY <2>c, <3>eqidx
    <3>domA. i - 2 \in 1..K  BY <3>x
    <3>domB. (i-2)+1 \in 1..K  BY <3>x
    <3>lt. (i-2) < (i-2)+1  OBVIOUS
    <3>rrTran. seq[(i-2)+1].rr \in Tran(seq[i-2].rr)  BY <3>domA, <3>domB, <3>lt, <1>tcpB
    <3>sub. l[i+1] \subseteq l[i]
      <4>m. seq[i-2].rr \in Messages
        <5>1. seq[i-2].rr \in CL  BY <1>tcpA, <3>domA
        <5> QED BY <5>1, <1>mi, TranClosureClosed
      <4>1. Caught(seq[(i-2)+1].rr) \subseteq Caught(seq[i-2].rr)
        BY <3>rrTran, <4>m, <1>mi, CaughtMonotoneTran
      <4> QED BY <4>1, <3>li, <3>li1
    <3>jltK. (i-2)+1 < K  BY <3>x
    <3>diffCon. Con(alpha, seq[i-2].rr) # Con(alpha, seq[(i-2)+1].rr)
      BY <3>domA, <3>domB, <3>lt, <3>jltK, <1>tcpC
    <3>diff. ConFromCaught(alpha, l[i]) # ConFromCaught(alpha, l[i+1])
      <4>1. ConFromCaught(alpha, Caught(seq[i-2].rr)) # ConFromCaught(alpha, Caught(seq[(i-2)+1].rr))
        BY <3>diffCon DEF Con
      <4> QED BY <4>1, <3>li, <3>li1
    <3> QED BY <3>sub, <3>diff
  <2> QED BY <2>a, <2>b, <2>c
<1>valid. l \in ValidSeqs(alpha)
  <2>idx. 1..(Len(l)-1) = 1..K  BY <1>llen
  <2> QED BY <1>lseq, <1>trans, <2>idx DEF ValidSeqs
<1>bound. Len(l) - 1 <= MaxDepth(alpha)  BY <1>valid, <1>lg, ValidSeqsLenMaxDepth
<1> QED BY <1>bound, <1>llen
====================================================================
