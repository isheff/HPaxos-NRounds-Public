----------------------------- MODULE ChainHolds -----------------------------
EXTENDS HPaxosPlusCal, InitChain, ChainStep, InvHolds
LOCAL INSTANCE TLAPS

LEMMA ChainHolds == Spec => []SafeAcceptorChainInv
<1>1. Init => SafeAcceptorChainInv  BY InitChain
<1>2. Inv /\ SafeAcceptorChainInv /\ [Next]_vars => SafeAcceptorChainInv'  BY ChainStep
<1>3. Spec => []Inv  BY InvHolds
<1> QED BY <1>1, <1>2, <1>3, PTL DEF Spec
====================================================================
