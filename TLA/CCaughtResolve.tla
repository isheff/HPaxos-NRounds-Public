---------------------------- MODULE CCaughtResolve ----------------------------
EXTENDS MessageConcrete, CTranResolve, CMessageTranClosed, CCaughtSResolve

LEMMA CCaughtResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE Caught(x) = CCaughtS(CTran(x))
<1>1. Caught(x) = CaughtS(Tran(x))  BY DEF Caught
<1>2. Tran(x) = CTran(x)  BY CTranResolve
<1>3. CTran(x) \subseteq CMessages  BY CMessageTranClosed
<1>4. CaughtS(CTran(x)) = CCaughtS(CTran(x))  BY <1>3, CCaughtSResolve
<1> QED BY <1>1, <1>2, <1>4
=============================================================================
