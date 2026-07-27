------------------------------- MODULE AmNowBox -------------------------------
EXTENDS HPaxosPlusCal, AllMsgNetElem
LOCAL INSTANCE TLAPS

LEMMA AmNowBox ==
  ASSUME NEW allmessages
  PROVE  Spec => (IsAllMessagesEverSent(allmessages) => []AmNowT(allmessages))
<1>pe. \A xx : Spec => (IsAllMessagesEverSent(allmessages) => [](xx \in Msgs => xx \in allmessages))
  <2> SUFFICES ASSUME NEW xx
               PROVE Spec => (IsAllMessagesEverSent(allmessages) => [](xx \in Msgs => xx \in allmessages))
    OBVIOUS
  <2>1. Spec => (IsAllMessagesEverSent(allmessages) => AllMsgBoxOp(xx, allmessages))  BY AllMsgNetElem
  <2> QED  BY <2>1 DEF AllMsgBoxOp
<1> SUFFICES ASSUME Spec, IsAllMessagesEverSent(allmessages) PROVE []AmNowT(allmessages)  OBVIOUS
<1>peb. \A xx : [](xx \in Msgs => xx \in allmessages)  BY <1>pe
<1>ba. (\A xx : [](xx \in Msgs => xx \in allmessages))
       <=> ([](\A xx : xx \in Msgs => xx \in allmessages))  OBVIOUS
<1>rhs. [](\A xx : xx \in Msgs => xx \in allmessages)  BY <1>peb, <1>ba
<1> QED  BY <1>rhs DEF AmNowT
====================================================================
