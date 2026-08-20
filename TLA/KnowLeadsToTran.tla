-------------------------- MODULE KnowLeadsToTran --------------------------
\* For x inside Tran(pp), under TranFairness(pp):
\*   x \in Msgs ~> x \in known_messages[a],  by induction on Tran-depth.
\* This is the pre-weakening KnowLeadsTo restricted to Tran(pp): every
\* history element of a Tran(pp)-member is again in Tran(pp) (TranTrans), so
\* unconditional WF is available throughout and plain Msgs-membership sources
\* suffice.  All original Msgs-source bridges (BTCop, NBop, NetStable) are
\* reused unchanged.
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        TranSubMessages, TranExclusiveDecreasesTranSize,
        ConjPairLeadsToTran, BoxTranClosed, BoxKnownEq, NetBridge,
        BoxTgtProduct, NetStable, SubsetKnownStableW, LearnLeadsToTranW
LOCAL INSTANCE TLAPS

LEMMA KnowLeadsToTran ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         NEW pp \in Messages,
         NEW a \in LiveAcceptors, NEW x \in Messages, x \in Tran(pp)
  PROVE  (Spec /\ TranFairness(pp)) => ((x \in Msgs) ~> (x \in known_messages[a]))
<1>aS. a \in SafeAcceptors  BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
<1>mi. TranFinite /\ TranTrans /\ TranAcyclic /\ TypeOKMessageInterface
  BY DEF MessageInterfaceAssumptions
<1> DEFINE Q(n) == \A xx \in Messages :
                     (xx \in Tran(pp) /\ Cardinality(Tran(xx)) = n) => KLTT(pp, a, xx)
<1> HIDE DEF KLTT
<1>all. \A n \in Nat : Q(n)
  <2> HIDE DEF Q
  <2>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
    <3> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                        NEW xx \in Messages, xx \in Tran(pp), Cardinality(Tran(xx)) = n
                 PROVE KLTT(pp, a, xx)
      BY DEF Q
    <3>tesub. TranExclusive(xx) \subseteq Messages
      BY <1>mi, TranSubMessages DEF TranExclusive
    <3>tetp. TranExclusive(xx) \subseteq Tran(pp)
      <4>1. Tran(xx) \subseteq Tran(pp)  BY <1>mi DEF TranTrans
      <4> QED  BY <4>1 DEF TranExclusive
    <3>xtf. IsFiniteSet(Tran(xx))  BY <1>mi DEF TranFinite
    <3>tef. IsFiniteSet(TranExclusive(xx))  BY <3>xtf, FS_Subset DEF TranExclusive
    <3>ssf. IsFiniteSet({a} \X TranExclusive(xx))  BY <3>tef, FS_Singleton, FS_Product
    <3>sssub. {a} \X TranExclusive(xx) \subseteq SafeAcceptors \X Messages  BY <1>aS, <3>tesub
    <3>plt. \A p \in {a} \X TranExclusive(xx) : CPT_LT(pp, {xx}, p)
      <4> SUFFICES ASSUME NEW p \in {a} \X TranExclusive(xx)
                   PROVE CPT_LT(pp, {xx}, p)  OBVIOUS
      <4>pd. p[1] = a /\ p[2] \in TranExclusive(xx)  OBVIOUS
      <4>wm. p[2] \in Messages  BY <4>pd, <3>tesub
      <4>wtp. p[2] \in Tran(pp)  BY <4>pd, <3>tetp
      <4>wcard. Cardinality(Tran(p[2])) < n  BY <4>pd, <1>mi, TranExclusiveDecreasesTranSize
      <4>wnat. Cardinality(Tran(p[2])) \in Nat  BY <4>wm, <1>mi, FS_CardinalityType DEF TranFinite
      <4>klw. KLTT(pp, a, p[2])
        <5>1. Cardinality(Tran(p[2])) \in 0..(n-1)  BY <4>wcard, <4>wnat
        <5>2. Q(Cardinality(Tran(p[2])))
          <6> HIDE DEF Q
          <6> QED  BY <5>1
        <5> QED  BY <5>2, <4>wm, <4>wtp DEF Q
      <4>wl. (Spec /\ TranFairness(pp)) => ((p[2] \in Msgs) ~> (p[2] \in known_messages[a]))
        BY <4>klw DEF KLTT
      <4>box. Spec => [](({xx} \subseteq Msgs) => p[2] \in Msgs)
        <5>1. BTCop(xx, p[2])  BY <4>pd, <4>wm, BoxTranClosed
        <5> QED  BY <5>1 DEF BTCop
      <4>ltxw. (Spec /\ TranFairness(pp)) => (({xx} \subseteq Msgs) ~> (p[2] \in known_messages[a]))
        BY <4>wl, <4>box, PTL
      <4>bke. Spec => [](p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a])
        <5>1. BKEop(p, a)  BY <4>pd, BoxKnownEq
        <5> QED  BY <5>1 DEF BKEop
      <4> QED  BY <4>ltxw, <4>bke, PTL DEF CPT_LT
    <3>hyp. CPT_Hyp(pp, {xx}, {a} \X TranExclusive(xx))
      BY <3>ssf, <3>sssub, <3>plt DEF CPT_Hyp
    <3>conj. CPTLop(pp, {xx}, {a} \X TranExclusive(xx))
      BY <3>hyp, ConjPairLeadsToTran
    <3>conj0. (Spec /\ TranFairness(pp))
                => (({xx} \subseteq Msgs) ~> CP_Tgt({a} \X TranExclusive(xx)))
      BY <3>conj DEF CPTLop
    <3>nb. Spec => [](({xx} \subseteq Msgs) <=> (xx \in Msgs))
      <4>1. NBop(xx)  BY NetBridge
      <4> QED  BY <4>1 DEF NBop
    <3>conj1. (Spec /\ TranFairness(pp))
                => ((xx \in Msgs) ~> CP_Tgt({a} \X TranExclusive(xx)))
      BY <3>conj0, <3>nb, PTL
    <3>tgtbox. Spec => [](CP_Tgt({a} \X TranExclusive(xx))
                          <=> (TranExclusive(xx) \subseteq known_messages[a]))
      <4>1. BTPop(a, TranExclusive(xx))  BY BoxTgtProduct
      <4> QED  BY <4>1 DEF BTPop
    <3>conj2. (Spec /\ TranFairness(pp))
                => ((xx \in Msgs) ~> (TranExclusive(xx) \subseteq known_messages[a]))
      BY <3>conj1, <3>tgtbox, PTL
    <3>learn. (Spec /\ TranFairness(pp))
                => ((xx \in Msgs /\ TranExclusive(xx) \subseteq known_messages[a])
                     ~> (xx \in known_messages[a]))
      <4>1. LLTTop(pp, a, xx)  BY LearnLeadsToTranW
      <4> QED  BY <4>1 DEF LLTTop
    <3>netst. Spec => [](xx \in Msgs => [](xx \in Msgs))  BY NetStable
    <3>test. Spec => [](TranExclusive(xx) \subseteq known_messages[a]
                        => [](TranExclusive(xx) \subseteq known_messages[a]))
      <4>1. SKSop(a, TranExclusive(xx))  BY <1>aS, SubsetKnownStableW
      <4> QED  BY <4>1 DEF SKSop
    <3>conj3. (Spec /\ TranFairness(pp))
                => ((xx \in Msgs)
                     ~> (xx \in Msgs /\ TranExclusive(xx) \subseteq known_messages[a]))
      BY <3>conj2, <3>netst, <3>test, PTL
    <3>kxx. (Spec /\ TranFairness(pp)) => ((xx \in Msgs) ~> (xx \in known_messages[a]))
      BY <3>conj3, <3>learn, PTL
    <3> QED  BY <3>kxx DEF KLTT
  <2> QED  BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>cn. Cardinality(Tran(x)) \in Nat  BY <1>mi, FS_CardinalityType DEF TranFinite
<1>qx. Q(Cardinality(Tran(x)))
  <2> HIDE DEF Q
  <2> QED  BY <1>all, <1>cn
<1>kx. KLTT(pp, a, x)  BY <1>qx DEF Q
<1> QED  BY <1>kx DEF KLTT
====================================================================
