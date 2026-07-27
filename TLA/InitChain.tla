----------------------------- MODULE InitChain -----------------------------
EXTENDS HPaxosPlusCal

LEMMA InitChain == Init => SafeAcceptorChainInv
<1> SUFFICES ASSUME Init PROVE SafeAcceptorChainInv  OBVIOUS
<1>1. Msgs = {}  BY DEF Init
<1> QED BY <1>1 DEF SafeAcceptorChainInv
====================================================================
