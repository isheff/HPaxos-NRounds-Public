---------------------------- MODULE InitSelfSentT ----------------------------
EXTENDS HPaxosPlusCal

LEMMA InitSelfSentT == Init => SelfSentBoundedInvT
<1> SUFFICES ASSUME Init PROVE SelfSentBoundedInvT  OBVIOUS
<1>1. Msgs = {}  BY DEF Init
<1> QED BY <1>1 DEF SelfSentBoundedInvT
====================================================================
