----------------------------- MODULE KnownDiaMem -----------------------------
\* An ever-known-set member is eventually on the network: mm \in am gives
\* <>KnownToLive(mm), and a known message is a sent message (Inv).  The
\* ever-known replacement for reading DiaMem straight off IAMESCond.
EXTENDS HPaxosPlusCal, InvHolds
LOCAL INSTANCE TLAPS

LEMMA KnownDiaMem ==
  ASSUME AcceptorsAssumptions, NEW am, NEW mm
  PROVE  Spec => (IsAllMessagesEverKnown(am) => (mm \in am => DiaMem(mm)))
<1>kb. Spec => [](KnownToLive(mm) => mm \in Msgs)
  <2>1. Inv /\ KnownToLive(mm) => mm \in Msgs
    BY DEF Inv, KnownToLive, AcceptorsAssumptions, LiveAcceptorsAssumption
  <2>2. Spec => []Inv  BY InvHolds
  <2> QED  BY <2>1, <2>2, PTL DEF Spec
<1> SUFFICES ASSUME Spec, IsAllMessagesEverKnown(am), mm \in am
             PROVE  DiaMem(mm)
  OBVIOUS
<1>kbb. [](KnownToLive(mm) => mm \in Msgs)  BY <1>kb
<1>equiv. mm \in am <=> (mm \in Messages /\ <>KnownToLive(mm))
  <2>1. \A z : (z \in am <=> IAMEKCond(z))  BY DEF IsAllMessagesEverKnown
  <2> HIDE DEF IAMEKCond
  <2>2. mm \in am <=> IAMEKCond(mm)  BY <2>1
  <2> QED  BY <2>2 DEF IAMEKCond
<1>dk. <>KnownToLive(mm)  BY <1>equiv, PTL
<1> QED  BY <1>dk, <1>kbb, PTL DEF DiaMem
====================================================================
