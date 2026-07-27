----------------------------- MODULE KnownSubAll -----------------------------
EXTENDS HPaxosPlusCal, KnownSubNet, AllMsgNetElem
LOCAL INSTANCE TLAPS

LEMMA KnownSubAll ==
  ASSUME NEW s \in SafeAcceptors, NEW am
  PROVE  Spec => (IsAllMessagesEverSent(am) => KnownAllBoxOp(s, am))
<1>kn. Spec => KnownNetBoxOp(s)  BY KnownSubNet
<1>pe. \A xx : Spec => (IsAllMessagesEverSent(am) => [](xx \in Msgs => xx \in am))
  <2> SUFFICES ASSUME NEW xx PROVE Spec => (IsAllMessagesEverSent(am) => [](xx \in Msgs => xx \in am))
    OBVIOUS
  <2>1. Spec => (IsAllMessagesEverSent(am) => AllMsgBoxOp(xx, am))  BY AllMsgNetElem
  <2> QED  BY <2>1 DEF AllMsgBoxOp
<1> SUFFICES ASSUME Spec, IsAllMessagesEverSent(am) PROVE KnownAllBoxOp(s, am)  OBVIOUS
<1>knb. [](\A xx : xx \in known_messages[s] => xx \in Msgs)  BY <1>kn DEF KnownNetBoxOp
<1>peb. \A xx : [](xx \in Msgs => xx \in am)  BY <1>pe
<1>bk. (\A xx : [](xx \in known_messages[s] => xx \in Msgs))
       <=> ([](\A xx : xx \in known_messages[s] => xx \in Msgs))  OBVIOUS
<1>bkn. \A xx : [](xx \in known_messages[s] => xx \in Msgs)  BY <1>knb, <1>bk
<1>per. \A xx : [](xx \in known_messages[s] => xx \in am)
  <2> SUFFICES ASSUME NEW xx PROVE [](xx \in known_messages[s] => xx \in am)  OBVIOUS
  <2>1. [](xx \in known_messages[s] => xx \in Msgs)  BY <1>bkn
  <2>2. [](xx \in Msgs => xx \in am)  BY <1>peb
  <2> QED  BY <2>1, <2>2, PTL
<1>ba. (\A xx : [](xx \in known_messages[s] => xx \in am))
       <=> ([](\A xx : xx \in known_messages[s] => xx \in am))  OBVIOUS
<1> QED  BY <1>per, <1>ba DEF KnownAllBoxOp
====================================================================
