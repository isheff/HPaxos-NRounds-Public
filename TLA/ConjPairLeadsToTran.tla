------------------------ MODULE ConjPairLeadsToTran ------------------------
\* Finite conjunction of leads-to, TranFairness flavour: the CPT_* operators
\* (kept in HPaxosPlusCal) mirror CP_* with hypothesis TranFairness(pp) and
\* plain Msgs-membership sources.  The proof is ConjPairLeadsTo's verbatim
\* with the fairness atom swapped; the target-side machinery (CP_Tgt,
\* BoxTgtEmpty, BoxTgtSplit, KnownStablePair) is shared unchanged.
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        BoxTgtEmpty, BoxTgtSplit, KnownStablePair
LOCAL INSTANCE TLAPS

LEMMA ConjPairLeadsToTran ==
  ASSUME NEW pp, NEW SS, NEW Src, CPT_Hyp(pp, Src, SS)
  PROVE  CPTLop(pp, Src, SS)
<1> DEFINE Q(n) == \A U : (CPT_Hyp(pp, Src, U) /\ Cardinality(U) = n) => CPT_Good(pp, Src, U)
<1> HIDE DEF CPT_LT, CPT_Good, CPT_Hyp
<1>all. \A n \in Nat : Q(n)
  <2> HIDE DEF Q
  <2>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
    <3> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                        NEW U, CPT_Hyp(pp, Src, U), Cardinality(U) = n
                 PROVE CPT_Good(pp, Src, U)
      BY DEF Q
    <3>hyp. /\ IsFiniteSet(U) /\ U \subseteq SafeAcceptors \X Messages
            /\ \A q \in U : CPT_LT(pp, Src, q)
      BY DEF CPT_Hyp
    <3>1. CASE U = {}
      <4>box. Spec => [](CP_Tgt(U))  BY <3>1, BoxTgtEmpty
      <4>2. (Spec /\ TranFairness(pp)) => ((Src \subseteq Msgs) ~> CP_Tgt(U))
        BY <4>box, PTL
      <4>3. Spec => [](CP_Tgt(U) => []CP_Tgt(U))  BY <4>box, PTL
      <4> QED  BY <4>2, <4>3 DEF CPT_Good
    <3>2. CASE U # {}
      <4>0. PICK p0 \in U : TRUE  BY <3>2
      <4> DEFINE U0 == U \ {p0}
      <4>card. Cardinality(U) >= 1  BY <3>hyp, FS_EmptySet, FS_CardinalityType
      <4>n1. n - 1 \in Nat  BY <4>card
      <4>U0f. IsFiniteSet(U0) /\ Cardinality(U0) = n - 1  BY <3>hyp, <4>0, FS_RemoveElement
      <4>U0h. CPT_Hyp(pp, Src, U0)
        <5>1. \A q \in U0 : CPT_LT(pp, Src, q)  BY <3>hyp
        <5> QED  BY <4>U0f, <3>hyp, <5>1 DEF CPT_Hyp
      <4>gU0. CPT_Good(pp, Src, U0)
        <5>k. n - 1 \in 0..(n-1)  BY <4>n1
        <5>q. Q(n - 1)  BY <5>k
        <5>a. (CPT_Hyp(pp, Src, U0) /\ Cardinality(U0) = n - 1) => CPT_Good(pp, Src, U0)
          BY <5>q DEF Q
        <5> QED  BY <5>a, <4>U0h, <4>U0f
      <4>lt0. (Spec /\ TranFairness(pp)) => ((Src \subseteq Msgs) ~> CP_Tgt(U0))
        BY <4>gU0 DEF CPT_Good
      <4>st0. Spec => [](CP_Tgt(U0) => []CP_Tgt(U0))  BY <4>gU0 DEF CPT_Good
      <4>p0m. p0[1] \in SafeAcceptors /\ p0[2] \in Messages  BY <4>0, <3>hyp
      <4>p0lt0. \A q \in U : CPT_LT(pp, Src, q)  BY <3>hyp
      <4>p0lt. (Spec /\ TranFairness(pp))
                 => ((Src \subseteq Msgs) ~> (p0[2] \in known_messages[p0[1]]))
        <5>1. CPT_LT(pp, Src, p0)  BY <4>p0lt0, <4>0
        <5> QED  BY <5>1 DEF CPT_LT
      <4>p0pair. p0 \in SafeAcceptors \X Messages  BY <4>0, <3>hyp
      <4>p0st. Spec => [](p0[2] \in known_messages[p0[1]]
                          => [](p0[2] \in known_messages[p0[1]]))
        BY <4>p0pair, KnownStablePair
      <4>boxsplit. Spec => [](CP_Tgt(U) <=> (CP_Tgt(U0) /\ p0[2] \in known_messages[p0[1]]))
        BY <4>0, BoxTgtSplit
      <4>ltU. (Spec /\ TranFairness(pp)) => ((Src \subseteq Msgs) ~> CP_Tgt(U))
        <5>1. (Spec /\ TranFairness(pp))
                => ((Src \subseteq Msgs) ~> (CP_Tgt(U0) /\ p0[2] \in known_messages[p0[1]]))
          BY <4>lt0, <4>p0lt, <4>st0, <4>p0st, PTL
        <5> QED  BY <5>1, <4>boxsplit, PTL
      <4>stU. Spec => [](CP_Tgt(U) => []CP_Tgt(U))
        <5>1. Spec => [](CP_Tgt(U0) /\ p0[2] \in known_messages[p0[1]]
                         => [](CP_Tgt(U0) /\ p0[2] \in known_messages[p0[1]]))
          BY <4>st0, <4>p0st, PTL
        <5> QED  BY <5>1, <4>boxsplit, PTL
      <4> QED  BY <4>ltU, <4>stU DEF CPT_Good
    <3> QED  BY <3>1, <3>2
  <2> QED  BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>cn. Cardinality(SS) \in Nat  BY FS_CardinalityType DEF CPT_Hyp
<1>qss. Q(Cardinality(SS))
  <2> HIDE DEF Q
  <2> QED  BY <1>all, <1>cn
<1>gss. CPT_Good(pp, Src, SS)
  <2>1. (CPT_Hyp(pp, Src, SS) /\ Cardinality(SS) = Cardinality(SS)) => CPT_Good(pp, Src, SS)
    BY <1>qss DEF Q
  <2> QED  BY <2>1
<1> QED  BY <1>gss DEF CPT_Good, CPTLop
====================================================================
