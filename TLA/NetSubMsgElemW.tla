--------------------------- MODULE NetSubMsgElemW ---------------------------
EXTENDS HPaxosPlusCal, NetSubMsgElem

LEMMA NetSubMsgElemW ==
  ASSUME NEW y
  PROVE  Spec => NetMsgBoxOp(y)
BY NetSubMsgElem DEF NetMsgBoxOp
====================================================================
