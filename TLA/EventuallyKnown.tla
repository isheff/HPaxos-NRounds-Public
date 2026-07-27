--------------------------- MODULE EventuallyKnown ---------------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        KnowLeadsToW, BoxMemInNet, ConjPairLeadsTo, BoxTgtLive,
        NetFiniteAlways, BoxFinImpNotSub
LOCAL INSTANCE TLAPS

\* Once a set of messages is all in Msgs, every live acceptor eventually knows
\* all of it.  We do NOT assume m is finite: whenever m \subseteq Msgs holds,
\* Msgs is finite (it starts empty and grows by at most one per step), so m is
\* finite there (infinite m: vacuous, since m can never be a subset of the
\* always-finite Msgs).
THEOREM EventuallyKnown ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions
  PROVE  Spec /\ NetworkAssumption =>
           \A m \in SUBSET Messages :
             (m \subseteq Msgs) ~>
             (\A a \in LiveAcceptors : m \subseteq known_messages[a])
<1>fa. IsFiniteSet(Acceptors)  BY DEF LearnerGraphAssumptions, FiniteAcceptors
<1>lsub. LiveAcceptors \subseteq Acceptors
  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption, LiveAcceptorsAssumption
<1>lfin. IsFiniteSet(LiveAcceptors)  BY <1>fa, <1>lsub, FS_Subset
<1> SUFFICES ASSUME NEW m \in SUBSET Messages
             PROVE  Spec /\ NetworkAssumption =>
                      ((m \subseteq Msgs) ~> (\A a \in LiveAcceptors : m \subseteq known_messages[a]))
  OBVIOUS
<1>fin. CASE IsFiniteSet(m)
  <2>ssf. IsFiniteSet(LiveAcceptors \X m)  BY <1>lfin, <1>fin, FS_Product
  <2>sssub. LiveAcceptors \X m \subseteq SafeAcceptors \X Messages
    BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
  <2>plt. \A p \in LiveAcceptors \X m : CP_LT(m, p)
    <3> SUFFICES ASSUME NEW p \in LiveAcceptors \X m PROVE CP_LT(m, p)  OBVIOUS
    <3>pd. p[1] \in LiveAcceptors /\ p[2] \in m  OBVIOUS
    <3>pm. p[2] \in Messages  BY <3>pd
    <3>kl. KLT(p[1], p[2])  BY <3>pd, <3>pm, KnowLeadsToW
    <3>klu. (Spec /\ NetworkAssumption) => ((p[2] \in Msgs) ~> (p[2] \in known_messages[p[1]]))
      BY <3>kl DEF KLT
    <3>box. Spec => [](m \subseteq Msgs => p[2] \in Msgs)
      <4>1. BMNop(m, p[2])  BY <3>pd, BoxMemInNet
      <4> QED  BY <4>1 DEF BMNop
    <3> QED  BY <3>klu, <3>box, PTL DEF CP_LT
  <2>hyp. CP_Hyp(m, LiveAcceptors \X m)  BY <2>ssf, <2>sssub, <2>plt DEF CP_Hyp
  <2>conj. CPLop(m, LiveAcceptors \X m)  BY <2>hyp, ConjPairLeadsTo
  <2>conj0. (Spec /\ NetworkAssumption)
              => ((m \subseteq Msgs) ~> CP_Tgt(LiveAcceptors \X m))
    BY <2>conj DEF CPLop
  <2>tb. Spec => [](CP_Tgt(LiveAcceptors \X m) <=> ELtgt(m))
    <3>1. BTLop(m)  BY BoxTgtLive
    <3> QED  BY <3>1 DEF BTLop
  <2>et. (Spec /\ NetworkAssumption) => ((m \subseteq Msgs) ~> ELtgt(m))
    BY <2>conj0, <2>tb, PTL
  <2> QED  BY <2>et DEF ELtgt
<1>inf. CASE ~IsFiniteSet(m)
  <2>fin2. Spec => [](IsFiniteSet(Msgs))  BY NetFiniteAlways
  <2>imp. Spec => [](IsFiniteSet(Msgs) => ~(m \subseteq Msgs))  BY <1>inf, BoxFinImpNotSub
  <2>ns. Spec => [](~(m \subseteq Msgs))  BY <2>fin2, <2>imp, PTL
  <2> QED  BY <2>ns, PTL
<1> QED  BY <1>fin, <1>inf
====================================================================
