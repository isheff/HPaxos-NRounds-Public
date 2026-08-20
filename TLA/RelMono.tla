------------------------------ MODULE RelMono ------------------------------
EXTENDS HPaxosPlusCal, NetMono, KnownMono
LOCAL INSTANCE TLAPS

\* RelevantMsgs membership is preserved by every step (Msgs and
\* known_messages only grow; Sig is constant).  Action-level companion of
\* RelStable, mirroring the NetMono/NetStable split.
LEMMA RelMono ==
  ASSUME AcceptorsAssumptions, NEW xx
  PROVE  Inv /\ (xx \in RelevantMsgs) /\ [Next]_vars => (xx \in RelevantMsgs)'
<1> SUFFICES ASSUME Inv, xx \in RelevantMsgs, [Next]_vars
             PROVE (xx \in RelevantMsgs)'  OBVIOUS
<1>net. Msgs \subseteq Msgs'  BY NetMono
<1>xm. xx \in Msgs /\ LiveRelevant(xx)  BY DEF RelevantMsgs
<1>xm2. xx \in Msgs'  BY <1>net, <1>xm
<1>rel. LiveRelevant(xx)'
  <2>c1. CASE Sig(xx) \in LiveAcceptors  BY <2>c1 DEF LiveRelevant
  <2>c2. CASE \E b \in LiveAcceptors : xx \in known_messages[b]
    <3> PICK b \in LiveAcceptors : xx \in known_messages[b]  BY <2>c2
    <3>bs. b \in SafeAcceptors
      BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
    <3>mono. known_messages[b] \subseteq known_messages'[b]
      BY KnownMono, <3>bs
    <3> QED  BY <3>mono DEF LiveRelevant
  <2> QED  BY <2>c1, <2>c2, <1>xm DEF LiveRelevant
<1> QED  BY <1>xm2, <1>rel DEF RelevantMsgs
====================================================================
