---------------------------- MODULE AllMsgRelElem ----------------------------
\* Anything LIVE-RELEVANT on the network is in allmessages (= the ever-KNOWN
\* set), boxed.  The fairness-powered replacement of the old AllMsgNetElem:
\* a live-relevant sent message is eventually known to a live acceptor
\* (KnowLeadsTo, under the weakened NetworkAssumption), hence satisfies
\* IAMEKCond.  Reusable per-element engine for []HighNowT / []LowNowT /
\* []AmNowT and the witness bridges.
\*
\* The Spec => [](...) pieces are proven BEFORE the SUFFICES brings the
\* raw-temporal hypotheses (NetworkAssumption, IsAllMessagesEverKnown) into
\* the ambient -- those silently disable PTL's necessitation.
EXTENDS HPaxosPlusCal, KnowLeadsToW, InvHolds
LOCAL INSTANCE TLAPS

LEMMA AllMsgRelElem ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         LiveAcceptors # {},
         NEW allmessages, NEW w
  PROVE  (Spec /\ NetworkAssumption)
           => (IsAllMessagesEverKnown(allmessages) => RelAllBoxOp(w, allmessages))
<1> USE DEF RelAllBoxOp
<1> PICK a \in LiveAcceptors : TRUE  OBVIOUS
<1>rm. Spec => [](w \in RelevantMsgs => w \in Messages)
  <2>1. Inv /\ (w \in RelevantMsgs) => w \in Messages  BY DEF Inv, RelevantMsgs
  <2>2. Spec => []Inv  BY InvHolds
  <2> QED  BY <2>1, <2>2, PTL DEF Spec
<1>kb. Spec => [](w \in known_messages[a] => KnownToLive(w))
  <2>1. Init => (w \in known_messages[a] => KnownToLive(w))  BY DEF KnownToLive
  <2>2. (w \in known_messages[a] => KnownToLive(w)) /\ [Next]_vars
          => (w \in known_messages[a] => KnownToLive(w))'  BY DEF KnownToLive
  <2> QED  BY <2>1, <2>2, PTL DEF Spec
<1>rigM. [](w \in Messages) \/ []( ~(w \in Messages))  OBVIOUS
<1>rigAM. [](w \in allmessages) \/ []( ~(w \in allmessages))  OBVIOUS
<1> SUFFICES ASSUME Spec, NetworkAssumption, IsAllMessagesEverKnown(allmessages)
             PROVE  [](w \in RelevantMsgs => w \in allmessages)
  OBVIOUS
<1>rmb. [](w \in RelevantMsgs => w \in Messages)  BY <1>rm
<1>kbb. [](w \in known_messages[a] => KnownToLive(w))  BY <1>kb
<1>mcase1. CASE ~(w \in Messages)
  <2>nm. []( ~(w \in Messages))  BY <1>mcase1, <1>rigM, PTL
  <2>1. [](~(w \in RelevantMsgs))  BY <2>nm, <1>rmb, PTL
  <2> QED  BY <2>1, PTL
<1>mcase2. CASE w \in Messages
  <2>bm. [](w \in Messages)  BY <1>mcase2, <1>rigM, PTL
  <2>klt. KLT(a, w)  BY <1>mcase2, KnowLeadsToW
  <2>lt. (Spec /\ NetworkAssumption) => ((w \in RelevantMsgs) ~> (w \in known_messages[a]))
    BY <2>klt DEF KLT
  <2>lt2. (w \in RelevantMsgs) ~> (w \in known_messages[a])  BY <2>lt
  <2>ltk. (w \in RelevantMsgs) ~> KnownToLive(w)  BY <2>lt2, <1>kbb, PTL
  <2>equiv. w \in allmessages <=> (w \in Messages /\ <>KnownToLive(w))
    <3>1. \A mm : (mm \in allmessages <=> IAMEKCond(mm))  BY DEF IsAllMessagesEverKnown
    <3> HIDE DEF IAMEKCond
    <3>2. w \in allmessages <=> IAMEKCond(w)  BY <3>1
    <3> QED  BY <3>2 DEF IAMEKCond
  <2> QED  BY <2>ltk, <2>equiv, <2>bm, <1>rigAM, PTL
<1> QED  BY <1>mcase1, <1>mcase2
====================================================================
