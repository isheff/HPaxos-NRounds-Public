------------------------- MODULE TraceExistenceSlow -------------------------
\* The widest citation set in the split: the whole trace/depth/connectivity
\* stack. All EXTENDS -- every one shares MessageInterface with this module.
EXTENDS MessageInterface, FiniteSetTheorems,
        MaxDepthFiniteAcceptors, TranClosureClosed, TranSubMessages,
        TranCardNat, TranExclusiveDecreasesTranSize,
        SlowSupportWitness, TraceStepWitness,
        QdProperties, QdDepthMember, QdOneBFresh, HasDepthLrns,
        ExistsMinTranCardElement, ExistsLeastIndex,
        TraceCondCoreCongr, TraceCoreProperties,
        CaughtSubClosure, ConFromCaughtAntitone, ConMonotoneTran,
        ConFromCaughtSym, ConFromCaughtCondensedTrans,
        FreshTopConnected
LOCAL INSTANCE TLAPS

\* Slow-decision trace existence (paper Lemma 25's induction).  Induction on
\* i: the base element pairs himsg with a decision-quorum member
\* (SlowSupportWitness); the step extracts the next mm via FreshTopConnected
\* applied to rr_n at w = ss_n, realizes minimality by
\* ExistsMinTranCardElement, and re-witnesses rr/ss at the minimal mm by
\* TraceStepWitness, spending one depth level of budget.
LEMMA TraceExistenceSlow ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         ValueInterfaceAssumptions,
         NEW mset \in SUBSET Messages,
         NEW alpha \in Learners, NEW beta \in Learners,
         NEW lobal \in Ballots, NEW hibal \in Ballots,
         lobal < hibal,
         BalToVal(lobal) # BalToVal(hibal),
         DecisionSlow(mset, alpha, lobal),
         beta \in ConFromCaught(alpha, CaughtS(TranClosure(mset))),
         NEW himsg \in TranClosure(mset),
         B(himsg) = hibal,
         beta \in Lrns(himsg)
  PROVE \A i \in 0..MaxDepth(alpha) :
          \E seq \in [1..i+1 -> TraceElem] :
            \A x \in 1..i+1 :
              /\ TraceCondCoreMin(alpha, lobal, TranClosure(mset), himsg, seq, x)
              /\ TraceBudgetSlow(alpha, seq, x)
<1> DEFINE CL == TranClosure(mset)
<1> DEFINE MD == MaxDepth(alpha)
<1>mi. TypeOKMessageInterface /\ TranFinite /\ TranTrans /\ TranAcyclic /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>lg. FiniteAcceptors /\ FiniteLearners /\ LearnersNonEmpty /\ QuorumsNonEmpty
       /\ LearnersMightAgree /\ CondensedLearnerGraphAssumption /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>md. MD \in Nat /\ MD >= 1
  <2>1. MD \in 1..Cardinality(Acceptors)  BY <1>lg, MaxDepthFiniteAcceptors
  <2> QED BY <2>1
<1>clM. CL \subseteq Messages
  <2> SUFFICES ASSUME NEW y \in CL PROVE y \in Messages  OBVIOUS
  <2> QED BY <1>mi, TranClosureClosed
<1>hiM. himsg \in Messages  BY <1>clM
<1>hiTr. Tran(himsg) \subseteq CL  BY <1>mi, TranClosureClosed
<1>vhi. V(himsg) = BalToVal(hibal)  BY DEF V
<1> DEFINE Q(n) == n \in 0..MD =>
      \E sq0 \in [1..n+1 -> TraceElem] :
        \A x \in 1..n+1 :
          /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq0, x)
          /\ TraceBudgetSlow(alpha, sq0, x)
<1> SUFFICES \A n \in Nat : Q(n)
  <2>1. \A i \in 0..MD : i \in Nat  OBVIOUS
  <2> QED BY <2>1 DEF Q
<1> HIDE DEF Q
<1>ind. \A n \in Nat : (\A kk \in 0..(n-1) : Q(kk)) => Q(n)
  \* Q is kept FOLDED throughout the step (no blanket USE DEF Q): the
  \* ambient course-of-values hypothesis would otherwise expand inside
  \* every one of the ~950 obligations below and blow their contexts up.
  \* Only the two steps that genuinely unfold Q cite its definition.
  <2> SUFFICES ASSUME NEW n \in Nat, \A kk \in 0..(n-1) : Q(kk), n \in 0..MD
               PROVE \E sq0 \in [1..n+1 -> TraceElem] :
                       \A x \in 1..n+1 :
                         /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq0, x)
                         /\ TraceBudgetSlow(alpha, sq0, x)
    BY DEF Q
  <2>base. CASE n = 0
    <3> DEFINE oneF(z) == [xx \in 1..1 |-> z]
    <3> DEFINE C1 == {z \in TraceElem : TraceCondCore(alpha, lobal, CL, himsg, oneF(z), 1)}
    <3>onev. \A z \in TraceElem : oneF(z)[1] = z  OBVIOUS
    <3>lob. lobal < B(himsg)  OBVIOUS
    <3>w. PICK rrw \in Qd(beta, himsg, 1) : \E ssw \in Tran(rrw) :
            Sig(rrw) = Sig(ssw) /\ B(ssw) = lobal /\ HasDepth(alpha, ssw, MD)
      BY <3>lob, SlowSupportWitness
    <3>w2. PICK ssw \in Tran(rrw) :
             Sig(rrw) = Sig(ssw) /\ B(ssw) = lobal /\ HasDepth(alpha, ssw, MD)
      BY <3>w
    <3>rrwM. rrw \in Messages
      <4>1. rrw \in TranExclusive(himsg)  BY <3>w, <1>hiM, <1>mi, QdProperties
      <4>2. rrw \in Tran(himsg)  BY <4>1 DEF TranExclusive
      <4> QED BY <4>2, <1>hiM, <1>mi, TranSubMessages
    <3>sswM. ssw \in Messages  BY <3>w2, <3>rrwM, <1>mi, TranSubMessages
    <3> DEFINE zw == [mm |-> himsg, rr |-> rrw, ss |-> ssw, gamma |-> beta]
    <3>zwT. zw \in TraceElem  BY <1>hiM, <3>rrwM, <3>sswM DEF TraceElem
    <3>hself. himsg \in Tran(himsg)  BY DEF Tran
    <3>zwC. zw \in C1
      <4>v. oneF(zw)[1] = zw  BY <3>zwT, <3>onev
      <4> QED BY <4>v, <3>zwT, <3>hself, <3>lob, <3>w, <3>w2 DEF TraceCondCore
    <3>ne. C1 # {}  BY <3>zwC
    <3> DEFINE M1 == {z.mm : z \in C1}
    <3>m1sub. M1 \in SUBSET Messages
      <4> SUFFICES ASSUME NEW z \in C1 PROVE z.mm \in Messages  OBVIOUS
      <4> QED BY DEF TraceElem
    <3>m1ne. M1 # {}  BY <3>ne
    <3>min. PICK mst \in M1 : \A y \in M1 : TranCard(mst) <= TranCard(y)
      BY <1>mi, <3>m1sub, <3>m1ne, ExistsMinTranCardElement
    <3>z0. PICK z0 \in C1 : z0.mm = mst  BY <3>min
    <3>z0T. z0 \in TraceElem  BY <3>z0
    <3>z0v. oneF(z0)[1] = z0  BY <3>z0T, <3>onev
    <3>z0c. TraceCondCore(alpha, lobal, CL, himsg, oneF(z0), 1)  BY <3>z0
    <3>z0f. /\ mst \in Tran(himsg)
            /\ z0.gamma \in ConFromCaught(alpha, CaughtS(CL))
            /\ lobal < B(mst)
            /\ z0.gamma \in Lrns(mst)
            /\ V(mst) = V(himsg)
      BY <3>z0c, <3>z0v, <3>z0 DEF TraceCondCore
    <3>z0L. z0.gamma \in Learners  BY <3>z0T DEF TraceElem
    <3>mstCL. mst \in CL  BY <3>z0f, <1>hiTr
    <3>mstM. mst \in Messages  BY <3>mstCL, <1>clM
    <3>rw. PICK rr1 \in Qd(z0.gamma, mst, 1) : \E ss1 \in Tran(rr1) :
             Sig(rr1) = Sig(ss1) /\ B(ss1) = lobal /\ HasDepth(alpha, ss1, MD)
      BY <3>z0f, <3>z0L, <3>mstCL, SlowSupportWitness
    <3>rw2. PICK ss1 \in Tran(rr1) :
              Sig(rr1) = Sig(ss1) /\ B(ss1) = lobal /\ HasDepth(alpha, ss1, MD)
      BY <3>rw
    <3>rr1M. rr1 \in Messages
      <4>1. rr1 \in TranExclusive(mst)  BY <3>rw, <3>mstM, <3>z0L, <1>mi, QdProperties
      <4>2. rr1 \in Tran(mst)  BY <4>1 DEF TranExclusive
      <4> QED BY <4>2, <3>mstM, <1>mi, TranSubMessages
    <3>ss1M. ss1 \in Messages  BY <3>rw2, <3>rr1M, <1>mi, TranSubMessages
    <3> DEFINE z1 == [mm |-> mst, rr |-> rr1, ss |-> ss1, gamma |-> z0.gamma]
    <3>z1T. z1 \in TraceElem  BY <3>mstM, <3>rr1M, <3>ss1M, <3>z0L DEF TraceElem
    <3> DEFINE sq1 == oneF(z1)
    <3>z1v. sq1[1] = z1  BY <3>z1T, <3>onev
    <3>core1. TraceCondCore(alpha, lobal, CL, himsg, sq1, 1)
      BY <3>z1v, <3>z0f, <3>rw, <3>rw2 DEF TraceCondCore
    <3>min1. \A z \in TraceElem :
               TraceCondCore(alpha, lobal, CL, himsg, [sq1 EXCEPT ![1] = z], 1)
                 => Cardinality(Tran(sq1[1].mm)) <= Cardinality(Tran(z.mm))
      <4> SUFFICES ASSUME NEW z \in TraceElem,
                          TraceCondCore(alpha, lobal, CL, himsg, [sq1 EXCEPT ![1] = z], 1)
                   PROVE Cardinality(Tran(mst)) <= Cardinality(Tran(z.mm))
        BY <3>z1v
      <4>v. [sq1 EXCEPT ![1] = z][1] = z  OBVIOUS
      <4>v2. oneF(z)[1] = z  BY <3>onev
      <4>x1. 1 \in Nat  OBVIOUS
      <4>c. TraceCondCore(alpha, lobal, CL, himsg, oneF(z), 1)
        BY <4>v, <4>v2, <4>x1, TraceCondCoreCongr
      <4>zin. z \in C1  BY <4>c
      <4>zmm. z.mm \in M1  BY <4>zin
      <4> QED BY <4>zmm, <3>min DEF TranCard
    <3>bud1. TraceBudgetSlow(alpha, sq1, 1)
      <4>1. MD - 1 + 1 = MD  BY <1>md
      <4> QED BY <3>z1v, <3>rw2, <4>1 DEF TraceBudgetSlow
    <3>dom. sq1 \in [1..n+1 -> TraceElem]
      <4>1. 1..n+1 = 1..1  BY <2>base
      <4>2. sq1 \in [1..1 -> TraceElem]  BY <3>z1T
      <4> QED BY <4>1, <4>2
    <3>all. \A x \in 1..n+1 :
              /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq1, x)
              /\ TraceBudgetSlow(alpha, sq1, x)
      <4> SUFFICES ASSUME NEW x \in 1..n+1
                   PROVE /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq1, x)
                         /\ TraceBudgetSlow(alpha, sq1, x)
        OBVIOUS
      <4>1. x = 1  BY <2>base
      <4> QED BY <4>1, <3>core1, <3>min1, <3>bud1 DEF TraceCondCoreMin
    <3> QED BY <3>dom, <3>all
  <2>step. CASE n >= 1
    <3>ihq. Q(n-1)
      <4>1. n - 1 \in 0..(n-1)  BY <2>step
      <4> QED BY <4>1
    <3>iharg. n - 1 \in 0..MD  BY <2>step, <1>md
    <3>arith. (n-1)+1 = n  BY <2>step
    <3>ih. PICK sq \in [1..n -> TraceElem] :
             \A x \in 1..n :
               /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sq, x)
               /\ TraceBudgetSlow(alpha, sq, x)
      BY <3>ihq, <3>iharg, <3>arith DEF Q
    <3>coreAll. \A x \in 1..n : TraceCondCore(alpha, lobal, CL, himsg, sq, x)
      BY <3>ih DEF TraceCondCoreMin
    <3>tcp. /\ \A i \in 1..n : sq[i].mm \in CL /\ sq[i].rr \in CL /\ sq[i].ss \in CL
            /\ \A i, j \in 1..n : i < j => sq[j].rr \in Tran(sq[i].rr)
      <4>1. /\ \A i \in 1..n : /\ sq[i].mm \in CL
                               /\ sq[i].rr \in CL
                               /\ sq[i].ss \in CL
            /\ \A i, j \in 1..n : i < j => sq[j].rr \in Tran(sq[i].rr)
            /\ \A i, j \in 1..n : (i < j /\ j < n) =>
                 /\ Con(alpha, sq[i].rr) \subseteq Con(alpha, sq[j].rr)
                 /\ Con(alpha, sq[i].rr) # Con(alpha, sq[j].rr)
        BY <3>coreAll, TraceCoreProperties
      <4> QED BY <4>1
    <3>eltM. \A i \in 1..n : sq[i].mm \in Messages /\ sq[i].rr \in Messages /\ sq[i].ss \in Messages
      BY <3>tcp, <1>clM
    <3>eltL. \A i \in 1..n : sq[i].gamma \in Learners
      <4> SUFFICES ASSUME NEW i \in 1..n PROVE sq[i].gamma \in Learners  OBVIOUS
      <4>1. sq[i] \in TraceElem  OBVIOUS
      <4> QED BY <4>1 DEF TraceElem
    <3>ndom. n \in 1..n  BY <2>step
    <3>cn. TraceCondCore(alpha, lobal, CL, himsg, sq, n)  BY <3>coreAll, <3>ndom
    <3>i2. lobal < B(sq[n].mm)  BY <3>cn DEF TraceCondCore
    <3>i7. sq[n].gamma \in Lrns(sq[n].mm)  BY <3>cn DEF TraceCondCore
    <3>i8. sq[n].rr \in Qd(sq[n].gamma, sq[n].mm, 1)  BY <3>cn DEF TraceCondCore
    <3>i9. sq[n].ss \in Tran(sq[n].rr)  BY <3>cn DEF TraceCondCore
    <3>i13. B(sq[n].ss) = lobal  BY <3>cn DEF TraceCondCore
    <3>i14. V(sq[n].mm) = V(himsg)  BY <3>cn DEF TraceCondCore
    <3>imm. sq[n].mm \in Tran(himsg)  BY <3>cn DEF TraceCondCore
    <3>nM. sq[n].mm \in Messages /\ sq[n].rr \in Messages /\ sq[n].ss \in Messages
      BY <3>eltM, <3>ndom
    <3>nL. sq[n].gamma \in Learners  BY <3>eltL, <3>ndom
    <3>budn. HasDepth(alpha, sq[n].ss, MD - n + 1)
      <4>1. n <= MD  OBVIOUS
      <4>2. TraceBudgetSlow(alpha, sq, n)  BY <3>ih, <3>ndom
      <4> QED BY <4>1, <4>2 DEF TraceBudgetSlow
    <3>dep. MD - n + 1 \in Nat /\ MD - n + 1 >= 1  BY <1>md, <2>step
    <3>rrTE. sq[n].rr \in TranExclusive(sq[n].mm) /\ B(sq[n].rr) = B(sq[n].mm)
      BY <3>i8, <3>nM, <3>nL, <1>mi, QdProperties
    <3>gcon. sq[n].gamma \in Con(alpha, sq[n].rr)
      <4>a. CASE n = 1
        <5>1. sq[n].gamma \in ConFromCaught(alpha, CaughtS(CL))
          BY <3>cn, <4>a DEF TraceCondCore
        <5>2. sq[n].rr \in CL  BY <3>tcp, <3>ndom
        <5>3. Caught(sq[n].rr) \subseteq CaughtS(CL)  BY <5>2, <1>mi, CaughtSubClosure
        <5>4. ConFromCaught(alpha, CaughtS(CL)) \subseteq ConFromCaught(alpha, Caught(sq[n].rr))
          BY <5>3, ConFromCaughtAntitone
        <5> QED BY <5>1, <5>4 DEF Con
      <4>b. CASE n > 1
        <5>d. n - 1 \in 1..n  BY <4>b
        <5>1. sq[n].gamma \in Con(alpha, sq[n-1].rr)  BY <3>cn, <4>b DEF TraceCondCore
        <5>2. sq[n].mm \in Tran(sq[n-1].rr)  BY <3>cn, <4>b DEF TraceCondCore
        <5>3. sq[n].rr \in Tran(sq[n].mm)  BY <3>rrTE DEF TranExclusive
        <5>m. sq[n-1].rr \in Messages  BY <3>eltM, <5>d
        <5>4. Tran(sq[n].mm) \subseteq Tran(sq[n-1].rr)  BY <5>2, <5>m, <1>mi DEF TranTrans
        <5>5. sq[n].rr \in Tran(sq[n-1].rr)  BY <5>3, <5>4
        <5> QED BY <5>1, <5>5, <5>m, <1>mi, ConMonotoneTran
      <4> QED BY <4>a, <4>b, <2>step
    <3>acon. alpha \in Con(sq[n].gamma, sq[n].rr)
      <4>1. sq[n].gamma \in ConFromCaught(alpha, Caught(sq[n].rr))  BY <3>gcon DEF Con
      <4>2. alpha \in ConFromCaught(sq[n].gamma, Caught(sq[n].rr))
        BY <4>1, <3>nL, ConFromCaughtSym
      <4> QED BY <4>2 DEF Con
    <3>fr. IsOneB(sq[n].rr) /\ Fresh(sq[n].gamma, sq[n].rr)
      <4>1. IsOneB(sq[n].rr) /\ Fresh(sq[n].gamma, sq[n].rr) /\ Sig(sq[n].rr) \in Acceptors
        BY <3>i8, <3>nM, <3>nL, <1>mi, QdOneBFresh
      <4> QED BY <4>1
    <3>alrn. alpha \in Lrns(sq[n].ss)
      BY <3>budn, <3>dep, <3>nM, <1>mi, <1>lg, HasDepthLrns
    <3>vrr. V(sq[n].rr) = V(himsg)
      <4>1. V(sq[n].rr) = BalToVal(B(sq[n].mm))  BY <3>rrTE DEF V
      <4>2. V(sq[n].mm) = BalToVal(B(sq[n].mm))  BY DEF V
      <4> QED BY <4>1, <4>2, <3>i14
    <3>vne. V(sq[n].ss) # V(sq[n].rr)
      <4>1. V(sq[n].rr) = BalToVal(hibal)  BY <3>vrr, <1>vhi
      <4>2. V(sq[n].ss) = BalToVal(lobal)  BY <3>i13 DEF V
      <4> QED BY <4>1, <4>2
    <3>cap. Con(sq[n].gamma, sq[n].rr) \cap Lrns(sq[n].ss) # {}  BY <3>acon, <3>alrn
    <3>ftc. PICK p \in Tran(sq[n].rr) :
              B(p) > B(sq[n].ss) /\ V(p) = V(sq[n].rr)
              /\ Con(sq[n].gamma, sq[n].rr) \cap Lrns(p) # {}
      BY <1>mi, <3>nM, <3>nL, <3>fr, <3>i9, <3>vne, <3>cap, FreshTopConnected
    <3>pM. p \in Messages  BY <3>ftc, <3>nM, <1>mi, TranSubMessages
    <3>p2. lobal < B(p)  BY <3>ftc, <3>i13
    <3>p14. V(p) = V(himsg)  BY <3>ftc, <3>vrr
    <3>pcard. Cardinality(Tran(p)) < Cardinality(Tran(sq[n].mm))
      <4>1. Tran(p) \subseteq Tran(sq[n].rr)  BY <3>ftc, <3>nM, <1>mi DEF TranTrans
      <4>2. IsFiniteSet(Tran(sq[n].rr))  BY <3>nM, <1>mi DEF TranFinite
      <4>3. Cardinality(Tran(p)) <= Cardinality(Tran(sq[n].rr))  BY <4>1, <4>2, FS_Subset
      <4>4. Cardinality(Tran(sq[n].rr)) < Cardinality(Tran(sq[n].mm))
        BY <3>rrTE, <3>nM, <1>mi, TranExclusiveDecreasesTranSize
      <4>5. Cardinality(Tran(p)) \in Nat /\ Cardinality(Tran(sq[n].rr)) \in Nat
            /\ Cardinality(Tran(sq[n].mm)) \in Nat
        BY <3>pM, <3>nM, <1>mi, TranCardNat
      <4> QED BY <4>3, <4>4, <4>5
    <3>pTr. p \in Tran(himsg)
      <4>0. sq[n].rr \in Tran(sq[n].mm)  BY <3>rrTE DEF TranExclusive
      <4>1. Tran(sq[n].rr) \subseteq Tran(sq[n].mm)  BY <4>0, <3>nM, <1>mi DEF TranTrans
      <4>2. Tran(sq[n].mm) \subseteq Tran(himsg)  BY <3>imm, <1>hiM, <1>mi DEF TranTrans
      <4> QED BY <3>ftc, <4>1, <4>2
    <3>g. PICK gam \in Con(sq[n].gamma, sq[n].rr) \cap Lrns(p) : TRUE  BY <3>ftc
    <3>gf. gam \in Con(sq[n].gamma, sq[n].rr) /\ gam \in Lrns(p)  BY <3>g
    <3>gL. gam \in Learners  BY <3>gf DEF Con, ConFromCaught
    <3>g5. gam \in Con(alpha, sq[n].rr)
      <4>1. gam \in ConFromCaught(sq[n].gamma, Caught(sq[n].rr))  BY <3>gf DEF Con
      <4>2. sq[n].gamma \in ConFromCaught(alpha, Caught(sq[n].rr))  BY <3>gcon DEF Con
      <4>3. gam \in ConFromCaught(alpha, Caught(sq[n].rr))
        BY <1>lg, <4>1, <4>2, <3>nL, <3>gL, ConFromCaughtCondensedTrans
      <4> QED BY <4>3 DEF Con
    <3>i6. n >= 2 => gam \notin Con(alpha, sq[n-1].rr)
      <4> SUFFICES ASSUME n >= 2, gam \in Con(alpha, sq[n-1].rr) PROVE FALSE  OBVIOUS
      <4> DEFINE S == {idx \in 1..n : gam \in Con(alpha, sq[idx].rr)}
      <4>sn. S \in SUBSET Nat  OBVIOUS
      <4>nm1. n - 1 \in 1..n  OBVIOUS
      <4>ne. S # {}  BY <4>nm1
      <4>ks. PICK kst \in S : \A j \in S : kst <= j  BY <4>sn, <4>ne, ExistsLeastIndex
      <4>kf. kst \in 1..n /\ gam \in Con(alpha, sq[kst].rr)  BY <4>ks
      <4>kle. kst <= n - 1
        <5>1. n - 1 \in S  BY <4>nm1
        <5> QED BY <4>ks, <5>1
      <4>klt. kst < n /\ kst + 1 \in 1..n /\ kst >= 1  BY <4>kf, <4>kle
      <4>least. \A j \in 1..n : j < kst => gam \notin Con(alpha, sq[j].rr)
        <5> SUFFICES ASSUME NEW j \in 1..n, j < kst, gam \in Con(alpha, sq[j].rr)
                     PROVE FALSE
          OBVIOUS
        <5>1. j \in S  OBVIOUS
        <5>2. kst <= j  BY <4>ks, <5>1
        <5> QED BY <5>2
      <4>budk. HasDepth(alpha, sq[kst].ss, MD - kst + 1)
        <5>1. kst <= MD  BY <4>kf, <1>md
        <5>2. TraceBudgetSlow(alpha, sq, kst)  BY <3>ih, <4>kf
        <5> QED BY <5>1, <5>2 DEF TraceBudgetSlow
      <4>depk. MD - kst + 1 \in Nat /\ MD - kst + 1 >= 1  BY <1>md, <4>kf
      <4>ck. TraceCondCore(alpha, lobal, CL, himsg, sq, kst)  BY <3>coreAll, <4>kf
      <4>k9. sq[kst].ss \in Tran(sq[kst].rr)  BY <4>ck DEF TraceCondCore
      <4>k13. B(sq[kst].ss) = lobal  BY <4>ck DEF TraceCondCore
      <4>k8. sq[kst].rr \in Qd(sq[kst].gamma, sq[kst].mm, 1)  BY <4>ck DEF TraceCondCore
      <4>kM. sq[kst].mm \in Messages /\ sq[kst].rr \in Messages /\ sq[kst].ss \in Messages
        BY <3>eltM, <4>kf
      <4>kL. sq[kst].gamma \in Learners  BY <3>eltL, <4>kf
      <4>pk. p \in Tran(sq[kst].rr)
        <5>1. sq[n].rr \in Tran(sq[kst].rr)  BY <3>tcp, <4>kf, <4>klt, <3>ndom
        <5>2. Tran(sq[n].rr) \subseteq Tran(sq[kst].rr)  BY <5>1, <4>kM, <1>mi DEF TranTrans
        <5> QED BY <3>ftc, <5>2
      <4>tsw. PICK rrs \in Qd(gam, p, 1) : \E sss \in Qd(alpha, sq[kst].ss, MD - kst + 1) :
                Sig(rrs) = Sig(sss) /\ sss \in Tran(rrs)
        BY <4>kf, <3>gf, <4>pk, <4>k9, <4>k13, <3>p2, <4>budk, <4>depk,
           <4>kM, <3>pM, <3>gL, TraceStepWitness
      <4>tsw2. PICK sss \in Qd(alpha, sq[kst].ss, MD - kst + 1) :
                 Sig(rrs) = Sig(sss) /\ sss \in Tran(rrs)
        BY <4>tsw
      \* single-conjunct extractions: in this large context the provers
      \* handle a lemma application with an atomic goal, but not one with
      \* a conjunctive goal
      <4>sssP1. sss \in TranExclusive(sq[kst].ss)
        BY <4>tsw2, <4>kM, <1>mi, <4>depk, QdProperties
      <4>sssP2. B(sss) = B(sq[kst].ss)
        BY <4>tsw2, <4>kM, <1>mi, <4>depk, QdProperties
      <4>rrsM. rrs \in Messages
        <5>1. rrs \in TranExclusive(p)  BY <4>tsw, <3>pM, <3>gL, <1>mi, QdProperties
        <5>2. rrs \in Tran(p)  BY <5>1 DEF TranExclusive
        <5> QED BY <5>2, <3>pM, <1>mi, TranSubMessages
      <4>sssM. sss \in Messages  BY <4>tsw2, <4>rrsM, <1>mi, TranSubMessages
      <4> DEFINE wst == [mm |-> p, rr |-> rrs, ss |-> sss, gamma |-> gam]
      <4>wT. wst \in TraceElem  BY <3>pM, <4>rrsM, <4>sssM, <3>gL DEF TraceElem
      <4> DEFINE sqW == [sq EXCEPT ![kst+1] = wst]
      <4>wv. sqW[kst+1] = wst /\ sqW[kst] = sq[kst]
             /\ (kst >= 2 => sqW[kst-1] = sq[kst-1])
        BY <4>klt, <4>kf
      <4>c3. Cardinality(Tran(p)) < Cardinality(Tran(sq[kst].mm))
        <5>1. Tran(p) \subseteq Tran(sq[kst].rr)  BY <4>pk, <4>kM, <1>mi DEF TranTrans
        <5>2. IsFiniteSet(Tran(sq[kst].rr))  BY <4>kM, <1>mi DEF TranFinite
        <5>3. Cardinality(Tran(p)) <= Cardinality(Tran(sq[kst].rr))  BY <5>1, <5>2, FS_Subset
        <5>4. sq[kst].rr \in TranExclusive(sq[kst].mm)
          <6>1. sq[kst].rr \in TranExclusive(sq[kst].mm) /\ B(sq[kst].rr) = B(sq[kst].mm)
            BY <4>k8, <4>kM, <4>kL, <1>mi, QdProperties
          <6> QED BY <6>1
        <5>5. Cardinality(Tran(sq[kst].rr)) < Cardinality(Tran(sq[kst].mm))
          BY <5>4, <4>kM, <1>mi, TranExclusiveDecreasesTranSize
        <5>6. Cardinality(Tran(p)) \in Nat /\ Cardinality(Tran(sq[kst].rr)) \in Nat
              /\ Cardinality(Tran(sq[kst].mm)) \in Nat
          BY <3>pM, <4>kM, <1>mi, TranCardNat
        <5> QED BY <5>3, <5>5, <5>6
      <4>c6. kst + 1 > 2 => gam \notin Con(alpha, sq[kst-1].rr)
        <5> SUFFICES ASSUME kst + 1 > 2 PROVE gam \notin Con(alpha, sq[kst-1].rr)
          OBVIOUS
        <5>1. kst >= 2  OBVIOUS
        <5>2. kst - 1 \in 1..n /\ kst - 1 < kst  BY <5>1, <4>kf
        <5> QED BY <4>least, <5>2
      <4>coreW. TraceCondCore(alpha, lobal, CL, himsg, sqW, kst+1)
        <5>arith. (kst+1) - 1 = kst /\ (kst+1) - 2 = kst - 1 /\ kst + 1 > 1 /\ kst + 1 # 1
          BY <4>klt
        <5>s10. sss \in Tran(sq[kst].ss)  BY <4>sssP1 DEF TranExclusive
        <5>s13. B(sss) = lobal  BY <4>sssP2, <4>k13
        <5> QED BY <5>arith, <4>wv, <3>pTr, <3>p2, <4>c3, <4>pk, <4>kf, <4>c6,
                   <3>gf, <4>tsw, <4>tsw2, <5>s10, <5>s13, <3>p14
                DEF TraceCondCore
      <4>minK. TraceCondCoreMin(alpha, lobal, CL, himsg, sq, kst+1)  BY <3>ih, <4>klt
      <4>le. Cardinality(Tran(sq[kst+1].mm)) <= Cardinality(Tran(wst.mm))
        BY <4>minK, <4>wT, <4>coreW DEF TraceCondCoreMin
      <4>wmm. wst.mm = p  OBVIOUS
      <4>lt. Cardinality(Tran(p)) < Cardinality(Tran(sq[kst+1].mm))
        <5>k1. kst + 1 \in 1..n  BY <4>klt
        <5>ck1. TraceCondCore(alpha, lobal, CL, himsg, sq, kst+1)  BY <3>coreAll, <5>k1
        <5>k18. sq[kst+1].rr \in Qd(sq[kst+1].gamma, sq[kst+1].mm, 1)  BY <5>ck1 DEF TraceCondCore
        <5>k1M. sq[kst+1].mm \in Messages /\ sq[kst+1].rr \in Messages  BY <3>eltM, <5>k1
        <5>k1L. sq[kst+1].gamma \in Learners  BY <3>eltL, <5>k1
        <5>te. sq[kst+1].rr \in TranExclusive(sq[kst+1].mm)
          <6>1. sq[kst+1].rr \in TranExclusive(sq[kst+1].mm)
                /\ B(sq[kst+1].rr) = B(sq[kst+1].mm)
            BY <5>k18, <5>k1M, <5>k1L, <1>mi, QdProperties
          <6> QED BY <6>1
        <5>pk1. p \in Tran(sq[kst+1].rr)
          <6>a. CASE kst + 1 = n
            <7> QED BY <3>ftc, <6>a
          <6>b. CASE kst + 1 < n
            <7>1. sq[n].rr \in Tran(sq[kst+1].rr)  BY <3>tcp, <5>k1, <6>b, <3>ndom
            <7>2. Tran(sq[n].rr) \subseteq Tran(sq[kst+1].rr)  BY <7>1, <5>k1M, <1>mi DEF TranTrans
            <7> QED BY <3>ftc, <7>2
          <6> QED BY <6>a, <6>b, <4>klt
        <5>c1. Tran(p) \subseteq Tran(sq[kst+1].rr)  BY <5>pk1, <5>k1M, <1>mi DEF TranTrans
        <5>c2. IsFiniteSet(Tran(sq[kst+1].rr))  BY <5>k1M, <1>mi DEF TranFinite
        <5>c3. Cardinality(Tran(p)) <= Cardinality(Tran(sq[kst+1].rr))  BY <5>c1, <5>c2, FS_Subset
        <5>c4. Cardinality(Tran(sq[kst+1].rr)) < Cardinality(Tran(sq[kst+1].mm))
          BY <5>te, <5>k1M, <1>mi, TranExclusiveDecreasesTranSize
        <5>ty. Cardinality(Tran(p)) \in Nat /\ Cardinality(Tran(sq[kst+1].rr)) \in Nat
               /\ Cardinality(Tran(sq[kst+1].mm)) \in Nat
          BY <3>pM, <5>k1M, <1>mi, TranCardNat
        <5> QED BY <5>c3, <5>c4, <5>ty
      <4>ty2. Cardinality(Tran(p)) \in Nat /\ Cardinality(Tran(sq[kst+1].mm)) \in Nat
        <5>1. sq[kst+1].mm \in Messages  BY <3>eltM, <4>klt
        <5> QED BY <3>pM, <5>1, <1>mi, TranCardNat
      <4> QED BY <4>le, <4>wmm, <4>lt, <4>ty2
    <3>tswN. PICK rrp \in Qd(gam, p, 1) : \E ssp \in Qd(alpha, sq[n].ss, MD - n + 1) :
               Sig(rrp) = Sig(ssp) /\ ssp \in Tran(rrp)
      BY <3>g5, <3>gf, <3>ftc, <3>i9, <3>i13, <3>p2, <3>budn, <3>dep,
         <3>nM, <3>pM, <3>gL, TraceStepWitness
    <3>tswN2. PICK ssp \in Qd(alpha, sq[n].ss, MD - n + 1) :
                Sig(rrp) = Sig(ssp) /\ ssp \in Tran(rrp)
      BY <3>tswN
    <3>sspP1. ssp \in TranExclusive(sq[n].ss)
      BY <3>tswN2, <3>nM, <1>mi, <3>dep, QdProperties
    <3>sspP2. B(ssp) = B(sq[n].ss)
      BY <3>tswN2, <3>nM, <1>mi, <3>dep, QdProperties
    <3>rrpM. rrp \in Messages
      <4>1. rrp \in TranExclusive(p)  BY <3>tswN, <3>pM, <3>gL, <1>mi, QdProperties
      <4>2. rrp \in Tran(p)  BY <4>1 DEF TranExclusive
      <4> QED BY <4>2, <3>pM, <1>mi, TranSubMessages
    <3>sspM. ssp \in Messages  BY <3>tswN2, <3>rrpM, <1>mi, TranSubMessages
    <3> DEFINE seqE(z) == [xx \in 1..n+1 |-> IF xx = n+1 THEN z ELSE sq[xx]]
    <3>seqEv. \A z \in TraceElem :
                seqE(z)[n+1] = z /\ (\A xx \in 1..n : seqE(z)[xx] = sq[xx])
      OBVIOUS
    <3> DEFINE zp == [mm |-> p, rr |-> rrp, ss |-> ssp, gamma |-> gam]
    <3>zpT. zp \in TraceElem  BY <3>pM, <3>rrpM, <3>sspM, <3>gL DEF TraceElem
    <3>zpC. TraceCondCore(alpha, lobal, CL, himsg, seqE(zp), n+1)
      <4>arith. (n+1) - 1 = n /\ (n+1) - 2 = n - 1 /\ n + 1 > 1 /\ n + 1 # 1
                /\ (n + 1 > 2 <=> n >= 2)
        BY <2>step
      <4>v. seqE(zp)[n+1] = zp /\ seqE(zp)[n] = sq[n]
            /\ (n >= 2 => seqE(zp)[n-1] = sq[n-1])
        BY <3>zpT, <3>seqEv, <2>step
      <4>s10. ssp \in Tran(sq[n].ss)  BY <3>sspP1 DEF TranExclusive
      <4>s13. B(ssp) = lobal  BY <3>sspP2, <3>i13
      <4> QED BY <4>arith, <4>v, <3>pTr, <3>p2, <3>pcard, <3>ftc, <3>g5, <3>i6,
                 <3>gf, <3>tswN, <3>tswN2, <4>s10, <4>s13, <3>p14
              DEF TraceCondCore
    <3> DEFINE CC == {z \in TraceElem : TraceCondCore(alpha, lobal, CL, himsg, seqE(z), n+1)}
    <3>ccne. zp \in CC  BY <3>zpC, <3>zpT
    <3> DEFINE MM == {z.mm : z \in CC}
    <3>mmsub. MM \in SUBSET Messages
      <4> SUFFICES ASSUME NEW z \in CC PROVE z.mm \in Messages  OBVIOUS
      <4> QED BY DEF TraceElem
    <3>mmne. MM # {}  BY <3>ccne
    <3>minP. PICK mst \in MM : \A y \in MM : TranCard(mst) <= TranCard(y)
      BY <1>mi, <3>mmsub, <3>mmne, ExistsMinTranCardElement
    <3>zz0. PICK z0 \in CC : z0.mm = mst  BY <3>minP
    <3>z0C. TraceCondCore(alpha, lobal, CL, himsg, seqE(z0), n+1)  BY <3>zz0
    <3>z0T. z0 \in TraceElem  BY <3>zz0
    <3>z0L2. z0.gamma \in Learners  BY <3>z0T DEF TraceElem
    <3>z0v. seqE(z0)[n+1] = z0 /\ seqE(z0)[n] = sq[n]
            /\ (n >= 2 => seqE(z0)[n-1] = sq[n-1])
      BY <3>z0T, <3>seqEv, <2>step
    <3>z0f. /\ mst \in Tran(himsg)
            /\ lobal < B(mst)
            /\ Cardinality(Tran(mst)) < Cardinality(Tran(sq[n].mm))
            /\ mst \in Tran(sq[n].rr)
            /\ z0.gamma \in Con(alpha, sq[n].rr)
            /\ (n >= 2 => z0.gamma \notin Con(alpha, sq[n-1].rr))
            /\ z0.gamma \in Lrns(mst)
            /\ V(mst) = V(himsg)
      <4>arith. (n+1) - 1 = n /\ (n+1) - 2 = n - 1 /\ n + 1 > 1
                /\ (n + 1 > 2 <=> n >= 2)
        BY <2>step
      <4> QED BY <3>z0C, <3>z0v, <3>zz0, <4>arith DEF TraceCondCore
    <3>mstM2. mst \in Messages  BY <3>zz0, <3>mmsub
    <3>rwN. PICK rrf \in Qd(z0.gamma, mst, 1) : \E ssf \in Qd(alpha, sq[n].ss, MD - n + 1) :
              Sig(rrf) = Sig(ssf) /\ ssf \in Tran(rrf)
      BY <3>z0f, <3>i9, <3>i13, <3>budn, <3>dep, <3>nM, <3>mstM2, <3>z0L2,
         TraceStepWitness
    <3>rwN2. PICK ssf \in Qd(alpha, sq[n].ss, MD - n + 1) :
               Sig(rrf) = Sig(ssf) /\ ssf \in Tran(rrf)
      BY <3>rwN
    <3>ssfP1. ssf \in TranExclusive(sq[n].ss)
      BY <3>rwN2, <3>nM, <1>mi, <3>dep, QdProperties
    <3>ssfP2. B(ssf) = B(sq[n].ss)
      BY <3>rwN2, <3>nM, <1>mi, <3>dep, QdProperties
    <3>ssfP3. HasDepth(alpha, ssf, MD - n + 1 - 1)
      <4>1. ssf \in Qd(alpha, sq[n].ss, MD - n + 1)  BY <3>rwN2
      \* NB: binary - binds tighter than + in TLA+, so the goal's
      \* MD - n + 1 - 1 parses as (MD-n) + (1-1), NOT ((MD-n)+1) - 1;
      \* the equality is arithmetic (needs MD, n \in Nat), not reflexivity.
      <4>e. MD - n + 1 - 1 = (MD - n + 1) - 1  BY <1>md
      <4> QED BY <4>1, <4>e, <3>nM, <1>mi, <3>dep, QdDepthMember
    <3>rrfM. rrf \in Messages
      <4>1. rrf \in TranExclusive(mst)  BY <3>rwN, <3>mstM2, <3>z0L2, <1>mi, QdProperties
      <4>2. rrf \in Tran(mst)  BY <4>1 DEF TranExclusive
      <4> QED BY <4>2, <3>mstM2, <1>mi, TranSubMessages
    <3>ssfM. ssf \in Messages  BY <3>rwN2, <3>rrfM, <1>mi, TranSubMessages
    <3> DEFINE zf == [mm |-> mst, rr |-> rrf, ss |-> ssf, gamma |-> z0.gamma]
    <3>zfT. zf \in TraceElem  BY <3>mstM2, <3>rrfM, <3>ssfM, <3>z0L2 DEF TraceElem
    <3> DEFINE sqN == seqE(zf)
    <3>zfv. sqN[n+1] = zf /\ sqN[n] = sq[n] /\ (\A xx \in 1..n : sqN[xx] = sq[xx])
            /\ (n >= 2 => sqN[n-1] = sq[n-1])
      BY <3>zfT, <3>seqEv, <2>step
    <3>zfC. TraceCondCore(alpha, lobal, CL, himsg, sqN, n+1)
      <4>arith. (n+1) - 1 = n /\ (n+1) - 2 = n - 1 /\ n + 1 > 1 /\ n + 1 # 1
                /\ (n + 1 > 2 <=> n >= 2)
        BY <2>step
      <4>s10. ssf \in Tran(sq[n].ss)  BY <3>ssfP1 DEF TranExclusive
      <4>s13. B(ssf) = lobal  BY <3>ssfP2, <3>i13
      <4> QED BY <4>arith, <3>zfv, <3>z0f, <3>rwN, <3>rwN2, <4>s10, <4>s13
              DEF TraceCondCore
    <3>domN. sqN \in [1..n+1 -> TraceElem]
      <4> SUFFICES ASSUME NEW xx \in 1..n+1 PROVE sqN[xx] \in TraceElem  OBVIOUS
      <4>a. CASE xx = n+1  BY <4>a, <3>zfT, <3>zfv
      <4>b. CASE xx # n+1
        <5>1. xx \in 1..n  BY <4>b
        <5>2. sqN[xx] = sq[xx]  BY <5>1, <3>zfv
        <5> QED BY <5>1, <5>2
      <4> QED BY <4>a, <4>b
    <3>minN. \A z \in TraceElem :
               TraceCondCore(alpha, lobal, CL, himsg, [sqN EXCEPT ![n+1] = z], n+1)
                 => Cardinality(Tran(sqN[n+1].mm)) <= Cardinality(Tran(z.mm))
      <4> SUFFICES ASSUME NEW z \in TraceElem,
                          TraceCondCore(alpha, lobal, CL, himsg, [sqN EXCEPT ![n+1] = z], n+1)
                   PROVE Cardinality(Tran(mst)) <= Cardinality(Tran(z.mm))
        BY <3>zfv
      <4>v. [sqN EXCEPT ![n+1] = z][n+1] = z
            /\ [sqN EXCEPT ![n+1] = z][n] = sq[n]
            /\ (n >= 2 => [sqN EXCEPT ![n+1] = z][n-1] = sq[n-1])
        BY <3>zfv, <2>step
      <4>v2. seqE(z)[n+1] = z /\ seqE(z)[n] = sq[n]
             /\ (n >= 2 => seqE(z)[n-1] = sq[n-1])
        BY <3>seqEv, <2>step
      <4>arith. (n+1) - 1 = n /\ (n+1) - 2 = n - 1 /\ n + 1 \in Nat
                /\ (n + 1 > 2 <=> n >= 2)
        BY <2>step
      <4>cg. TraceCondCore(alpha, lobal, CL, himsg, seqE(z), n+1)
        BY <4>v, <4>v2, <4>arith, TraceCondCoreCongr
      <4>zin. z \in CC  BY <4>cg
      <4>zmm. z.mm \in MM  BY <4>zin
      <4> QED BY <4>zmm, <3>minP DEF TranCard
    <3>budN. TraceBudgetSlow(alpha, sqN, n+1)
      <4> SUFFICES ASSUME n+1 <= MD
                   PROVE HasDepth(alpha, sqN[n+1].ss, MD - (n+1) + 1)
        BY DEF TraceBudgetSlow
      <4>1. sqN[n+1].ss = ssf  BY <3>zfv
      <4>2. MD - (n+1) + 1 = MD - n + 1 - 1  BY <1>md, <2>step
      <4> QED BY <4>1, <4>2, <3>ssfP3
    <3>old. \A x \in 1..n :
              /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sqN, x)
              /\ TraceBudgetSlow(alpha, sqN, x)
      <4> SUFFICES ASSUME NEW x \in 1..n
                   PROVE /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sqN, x)
                         /\ TraceBudgetSlow(alpha, sqN, x)
        OBVIOUS
      <4>xN. x \in Nat  OBVIOUS
      <4>vals. sqN[x] = sq[x] /\ (x > 1 => sqN[x-1] = sq[x-1]) /\ (x > 2 => sqN[x-2] = sq[x-2])
        <5>1. sqN[x] = sq[x]  BY <3>zfv
        <5>2. x > 1 => sqN[x-1] = sq[x-1]
          <6> SUFFICES ASSUME x > 1 PROVE sqN[x-1] = sq[x-1]  OBVIOUS
          <6>1. x - 1 \in 1..n  OBVIOUS
          <6> QED BY <6>1, <3>zfv
        <5>3. x > 2 => sqN[x-2] = sq[x-2]
          <6> SUFFICES ASSUME x > 2 PROVE sqN[x-2] = sq[x-2]  OBVIOUS
          <6>1. x - 2 \in 1..n  OBVIOUS
          <6> QED BY <6>1, <3>zfv
        <5> QED BY <5>1, <5>2, <5>3
      <4>core. TraceCondCore(alpha, lobal, CL, himsg, sqN, x)
        BY <3>coreAll, <4>vals, <4>xN, TraceCondCoreCongr
      <4>minx. \A z \in TraceElem :
                 TraceCondCore(alpha, lobal, CL, himsg, [sqN EXCEPT ![x] = z], x)
                   => Cardinality(Tran(sqN[x].mm)) <= Cardinality(Tran(z.mm))
        <5> SUFFICES ASSUME NEW z \in TraceElem,
                            TraceCondCore(alpha, lobal, CL, himsg, [sqN EXCEPT ![x] = z], x)
                     PROVE Cardinality(Tran(sq[x].mm)) <= Cardinality(Tran(z.mm))
          BY <4>vals
        <5>v1. [sqN EXCEPT ![x] = z][x] = z /\ [sq EXCEPT ![x] = z][x] = z  OBVIOUS
        <5>v2. x > 1 => ([sqN EXCEPT ![x] = z][x-1] = sq[x-1]
                         /\ [sq EXCEPT ![x] = z][x-1] = sq[x-1])
          <6> SUFFICES ASSUME x > 1 PROVE [sqN EXCEPT ![x] = z][x-1] = sq[x-1]
                                          /\ [sq EXCEPT ![x] = z][x-1] = sq[x-1]
            OBVIOUS
          <6>1. x - 1 \in 1..n /\ x - 1 # x  OBVIOUS
          <6> QED BY <6>1, <3>zfv
        <5>v3. x > 2 => ([sqN EXCEPT ![x] = z][x-2] = sq[x-2]
                         /\ [sq EXCEPT ![x] = z][x-2] = sq[x-2])
          <6> SUFFICES ASSUME x > 2 PROVE [sqN EXCEPT ![x] = z][x-2] = sq[x-2]
                                          /\ [sq EXCEPT ![x] = z][x-2] = sq[x-2]
            OBVIOUS
          <6>1. x - 2 \in 1..n /\ x - 2 # x  OBVIOUS
          <6> QED BY <6>1, <3>zfv
        <5>cg. TraceCondCore(alpha, lobal, CL, himsg, [sq EXCEPT ![x] = z], x)
          BY <5>v1, <5>v2, <5>v3, <4>xN, TraceCondCoreCongr
        <5>ihm. TraceCondCoreMin(alpha, lobal, CL, himsg, sq, x)  BY <3>ih
        <5> QED BY <5>ihm, <5>cg DEF TraceCondCoreMin
      <4>budx. TraceBudgetSlow(alpha, sqN, x)
        <5>1. sqN[x].ss = sq[x].ss  BY <4>vals
        <5>2. TraceBudgetSlow(alpha, sq, x)  BY <3>ih
        <5> QED BY <5>1, <5>2 DEF TraceBudgetSlow
      <4> QED BY <4>core, <4>minx, <4>budx DEF TraceCondCoreMin
    <3>all. \A x \in 1..n+1 :
              /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sqN, x)
              /\ TraceBudgetSlow(alpha, sqN, x)
      <4> SUFFICES ASSUME NEW x \in 1..n+1
                   PROVE /\ TraceCondCoreMin(alpha, lobal, CL, himsg, sqN, x)
                         /\ TraceBudgetSlow(alpha, sqN, x)
        OBVIOUS
      <4>a. CASE x \in 1..n  BY <3>old, <4>a
      <4>b. CASE x = n+1
        BY <3>zfC, <3>minN, <3>budN, <4>b DEF TraceCondCoreMin
      <4> QED BY <4>a, <4>b
    <3> QED BY <3>domN, <3>all
  <2> QED BY <2>base, <2>step
<1> QED BY <1>ind, GeneralNatInduction, IsaM("blast")
====================================================================
