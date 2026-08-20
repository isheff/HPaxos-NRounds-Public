---------------------------- MODULE KnowLeadsTo ----------------------------
\* x \in RelevantMsgs ~> x \in known_messages[a], by induction on Tran-depth.
\* Op-wrapped conclusions (KLT, BTCRop, BKEop, NBRop, BTPop, SKSop, LLTop, all
\* kept in HPaxosPlusCal): temporal-conclusion lemmas can only be APPLIED with
\* identity/non-temporal parameters, so wrapping the conclusion in a top-level
\* op makes each instantiation first-order over the opaque symbol.
\*
\* WEAKENED: the source is membership in RelevantMsgs (live-relevant sent
\* messages) -- the weakened NetworkAssumption promises nothing beyond it.
\* The induction goes through because RelevantMsgs is TranExclusive-closed at
\* reachable states (BoxRelTranClosed).
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        TranSubMessages, TranExclusiveDecreasesTranSize,
        ConjPairLeadsTo, BoxRelTranClosed, BoxKnownEq, RelBridge,
        BoxTgtProduct, RelStable, SubsetKnownStableW, LearnLeadsToW
LOCAL INSTANCE TLAPS

LEMMA KnowLeadsTo ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         NEW a \in LiveAcceptors, NEW x \in Messages
  PROVE  (Spec /\ NetworkAssumption) => ((x \in RelevantMsgs) ~> (x \in known_messages[a]))
<1>aS. a \in SafeAcceptors  BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
<1>mi. TranFinite /\ TranTrans /\ TranAcyclic /\ TypeOKMessageInterface
  BY DEF MessageInterfaceAssumptions
<1> DEFINE Q(n) == \A xx \in Messages : Cardinality(Tran(xx)) = n => KLT(a, xx)
<1> HIDE DEF KLT
<1>all. \A n \in Nat : Q(n)
  <2> HIDE DEF Q
  <2>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
    <3> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                        NEW xx \in Messages, Cardinality(Tran(xx)) = n
                 PROVE KLT(a, xx)
      BY DEF Q
    <3>tesub. TranExclusive(xx) \subseteq Messages
      BY <1>mi, TranSubMessages DEF TranExclusive
    <3>xtf. IsFiniteSet(Tran(xx))  BY <1>mi DEF TranFinite
    <3>tef. IsFiniteSet(TranExclusive(xx))  BY <3>xtf, FS_Subset DEF TranExclusive
    <3>ssf. IsFiniteSet({a} \X TranExclusive(xx))  BY <3>tef, FS_Singleton, FS_Product
    <3>sssub. {a} \X TranExclusive(xx) \subseteq SafeAcceptors \X Messages  BY <1>aS, <3>tesub
    <3>plt. \A p \in {a} \X TranExclusive(xx) : CP_LT({xx}, p)
      <4> SUFFICES ASSUME NEW p \in {a} \X TranExclusive(xx)
                   PROVE CP_LT({xx}, p)  OBVIOUS
      <4>pd. p[1] = a /\ p[2] \in TranExclusive(xx)  OBVIOUS
      <4>wm. p[2] \in Messages  BY <4>pd, <3>tesub
      <4>wcard. Cardinality(Tran(p[2])) < n  BY <4>pd, <1>mi, TranExclusiveDecreasesTranSize
      <4>wnat. Cardinality(Tran(p[2])) \in Nat  BY <4>wm, <1>mi, FS_CardinalityType DEF TranFinite
      <4>klw. KLT(a, p[2])
        <5>1. Cardinality(Tran(p[2])) \in 0..(n-1)  BY <4>wcard, <4>wnat
        <5>2. Q(Cardinality(Tran(p[2])))
          <6> HIDE DEF Q
          <6> QED  BY <5>1
        <5> QED  BY <5>2, <4>wm DEF Q
      <4>wl. (Spec /\ NetworkAssumption) => ((p[2] \in RelevantMsgs) ~> (p[2] \in known_messages[a]))
        BY <4>klw DEF KLT
      <4>box. Spec => [](({xx} \subseteq RelevantMsgs) => p[2] \in RelevantMsgs)
        <5>1. BTCRop(xx, p[2])  BY <4>pd, <4>wm, BoxRelTranClosed
        <5> QED  BY <5>1 DEF BTCRop
      <4>ltxw. (Spec /\ NetworkAssumption) => (({xx} \subseteq RelevantMsgs) ~> (p[2] \in known_messages[a]))
        BY <4>wl, <4>box, PTL
      <4>bke. Spec => [](p[2] \in known_messages[p[1]] <=> p[2] \in known_messages[a])
        <5>1. BKEop(p, a)  BY <4>pd, BoxKnownEq
        <5> QED  BY <5>1 DEF BKEop
      <4> QED  BY <4>ltxw, <4>bke, PTL DEF CP_LT
    <3>hyp. CP_Hyp({xx}, {a} \X TranExclusive(xx))
      BY <3>ssf, <3>sssub, <3>plt DEF CP_Hyp
    <3>conj. CPLop({xx}, {a} \X TranExclusive(xx))
      BY <3>hyp, ConjPairLeadsTo
    <3>conj0. (Spec /\ NetworkAssumption)
                => (({xx} \subseteq RelevantMsgs) ~> CP_Tgt({a} \X TranExclusive(xx)))
      BY <3>conj DEF CPLop
    <3>nb. Spec => [](({xx} \subseteq RelevantMsgs) <=> (xx \in RelevantMsgs))
      <4>1. NBRop(xx)  BY RelBridge
      <4> QED  BY <4>1 DEF NBRop
    <3>conj1. (Spec /\ NetworkAssumption)
                => ((xx \in RelevantMsgs) ~> CP_Tgt({a} \X TranExclusive(xx)))
      BY <3>conj0, <3>nb, PTL
    <3>tgtbox. Spec => [](CP_Tgt({a} \X TranExclusive(xx))
                          <=> (TranExclusive(xx) \subseteq known_messages[a]))
      <4>1. BTPop(a, TranExclusive(xx))  BY BoxTgtProduct
      <4> QED  BY <4>1 DEF BTPop
    <3>conj2. (Spec /\ NetworkAssumption)
                => ((xx \in RelevantMsgs) ~> (TranExclusive(xx) \subseteq known_messages[a]))
      BY <3>conj1, <3>tgtbox, PTL
    <3>learn. (Spec /\ NetworkAssumption)
                => ((xx \in RelevantMsgs /\ TranExclusive(xx) \subseteq known_messages[a])
                     ~> (xx \in known_messages[a]))
      <4>1. LLTop(a, xx)  BY LearnLeadsToW
      <4> QED  BY <4>1 DEF LLTop
    <3>netst. Spec => [](xx \in RelevantMsgs => [](xx \in RelevantMsgs))
      <4>1. RelStableOp(xx)  BY RelStable
      <4> QED  BY <4>1 DEF RelStableOp
    <3>test. Spec => [](TranExclusive(xx) \subseteq known_messages[a]
                        => [](TranExclusive(xx) \subseteq known_messages[a]))
      <4>1. SKSop(a, TranExclusive(xx))  BY <1>aS, SubsetKnownStableW
      <4> QED  BY <4>1 DEF SKSop
    <3>conj3. (Spec /\ NetworkAssumption)
                => ((xx \in RelevantMsgs)
                     ~> (xx \in RelevantMsgs /\ TranExclusive(xx) \subseteq known_messages[a]))
      BY <3>conj2, <3>netst, <3>test, PTL
    <3>kxx. (Spec /\ NetworkAssumption) => ((xx \in RelevantMsgs) ~> (xx \in known_messages[a]))
      BY <3>conj3, <3>learn, PTL
    <3> QED  BY <3>kxx DEF KLT
  <2> QED  BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>cn. Cardinality(Tran(x)) \in Nat  BY <1>mi, FS_CardinalityType DEF TranFinite
<1>qx. Q(Cardinality(Tran(x)))
  <2> HIDE DEF Q
  <2> QED  BY <1>all, <1>cn
<1>kx. KLT(a, x)  BY <1>qx DEF Q
<1> QED  BY <1>kx DEF KLT
====================================================================
