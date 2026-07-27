---------------------------- MODULE FiniteDiamond ----------------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems, NaturalsInduction,
        SubStableOp, NetStableOp, FD_SplitBox, FD_EmptyBoxU
LOCAL INSTANCE TLAPS

LEMMA FiniteDiamond ==
  ASSUME Spec, NEW yy, FD_Hyp(yy)
  PROVE  FD_Good(yy)
<1> DEFINE Q(n) == \A U : (FD_Hyp(U) /\ Cardinality(U) = n) => FD_Good(U)
<1> HIDE DEF FD_Hyp, FD_Good, DiaMem
<1>all. \A n \in Nat : Q(n)
  <2> HIDE DEF Q
  <2>ind. \A n \in Nat : (\A k \in 0..(n-1) : Q(k)) => Q(n)
    <3> SUFFICES ASSUME NEW n \in Nat, \A k \in 0..(n-1) : Q(k),
                        NEW U, FD_Hyp(U), Cardinality(U) = n
                 PROVE FD_Good(U)
      BY DEF Q
    <3>fin. IsFiniteSet(U)  BY DEF FD_Hyp
    <3>dh. \A m \in U : DiaMem(m)  BY DEF FD_Hyp
    <3>1. CASE U = {}
      <4>e. <>(FD_Tgt(U))  BY <3>1, FD_EmptyBoxU
      <4> QED  BY <4>e DEF FD_Good
    <3>2. CASE U # {}
      <4>0. PICK p0 \in U : TRUE  BY <3>2
      <4> DEFINE U0 == U \ {p0}
      <4>card. Cardinality(U) >= 1  BY <3>2, <3>fin, FS_EmptySet, FS_CardinalityType
      <4>n1. n - 1 \in Nat  BY <4>card
      <4>U0f. IsFiniteSet(U0) /\ Cardinality(U0) = n - 1  BY <4>0, <3>fin, FS_RemoveElement
      <4>U0d. \A m \in U0 : DiaMem(m)  BY <3>dh
      <4>U0h. FD_Hyp(U0)  BY <4>U0f, <4>U0d DEF FD_Hyp
      <4>gU0. <>(FD_Tgt(U0))
        <5>q. Q(n - 1)  BY <4>n1
        <5>a. (FD_Hyp(U0) /\ Cardinality(U0) = n - 1) => FD_Good(U0)  BY <5>q DEF Q
        <5> QED  BY <5>a, <4>U0h, <4>U0f DEF FD_Good
      <4>p0d. <>(p0 \in Msgs)
        <5>1. DiaMem(p0)  BY <4>0, <3>dh
        <5> QED  BY <5>1 DEF DiaMem
      <4>stU0. [](FD_Tgt(U0) => []FD_Tgt(U0))
        <5>1. SubStabOp(U0)  BY SubStableOp
        <5> QED  BY <5>1 DEF SubStabOp, FD_Tgt
      <4>stp0. [](p0 \in Msgs => [](p0 \in Msgs))
        <5>1. ElStabOp(p0)  BY NetStableOp
        <5> QED  BY <5>1 DEF ElStabOp
      <4>conj. <>(FD_Tgt(U0) /\ p0 \in Msgs)
        BY <4>gU0, <4>p0d, <4>stU0, <4>stp0, PTL
      <4>split. Spec => [](FD_Tgt(U) <=> (FD_Tgt(U0) /\ p0 \in Msgs))  BY <4>0, FD_SplitBox
      <4> QED  BY <4>conj, <4>split, PTL DEF FD_Good
    <3> QED  BY <3>1, <3>2
  <2> QED  BY <2>ind, GeneralNatInduction, IsaM("blast")
<1>hyp. FD_Hyp(yy)  OBVIOUS
<1>fin2. IsFiniteSet(yy)  BY <1>hyp DEF FD_Hyp
<1>cn2. Cardinality(yy) \in Nat  BY <1>fin2, FS_CardinalityType
<1>q. Q(Cardinality(yy))
  <2> HIDE DEF Q
  <2> QED  BY <1>all, <1>cn2
<1>a. (FD_Hyp(yy) /\ Cardinality(yy) = Cardinality(yy)) => FD_Good(yy)  BY <1>q DEF Q
<1> QED  BY <1>a, <1>hyp
====================================================================
