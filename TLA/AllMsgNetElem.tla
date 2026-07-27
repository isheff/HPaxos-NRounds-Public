---------------------------- MODULE AllMsgNetElem ----------------------------
EXTENDS HPaxosPlusCal, NetSubMsgElemW
LOCAL INSTANCE TLAPS

\* Anything ever in Msgs is in allmessages (= the ever-sent set), boxed.
\* Reusable producer for []UniqNowT / []LowNowT.
LEMMA AllMsgNetElem ==
  ASSUME NEW allmessages, NEW w
  PROVE  Spec => (IsAllMessagesEverSent(allmessages) => AllMsgBoxOp(w, allmessages))
<1> SUFFICES ASSUME Spec
             PROVE  IsAllMessagesEverSent(allmessages) => AllMsgBoxOp(w, allmessages)
  OBVIOUS
<1>nmop. NetMsgBoxOp(w)  BY NetSubMsgElemW
<1>nm. [](w \in Msgs => w \in Messages)  BY <1>nmop DEF NetMsgBoxOp
<1>rigM. [](w \in Messages) \/ []( ~(w \in Messages))  OBVIOUS
<1>rigAM. [](w \in allmessages) \/ []( ~(w \in allmessages))  OBVIOUS
<1>dm. <>(w \in Msgs) => <>(w \in Messages)  BY <1>nm, PTL
<1>msg. <>(w \in Msgs) => (w \in Messages)  BY <1>dm, <1>rigM, PTL
<1> SUFFICES ASSUME IsAllMessagesEverSent(allmessages)
             PROVE  AllMsgBoxOp(w, allmessages)
  OBVIOUS
<1>equiv. w \in allmessages <=> (w \in Messages /\ <>(w \in Msgs))
  <2>1. \A mm : (mm \in allmessages <=> IAMESCond(mm))  BY DEF IsAllMessagesEverSent
  <2> HIDE DEF IAMESCond
  <2>2. w \in allmessages <=> IAMESCond(w)  BY <2>1
  <2> QED  BY <2>2 DEF IAMESCond
<1>x. <>(w \in Msgs) => w \in allmessages  BY <1>equiv, <1>msg, PTL
<1> QED  BY <1>x, <1>rigAM, PTL DEF AllMsgBoxOp
====================================================================
