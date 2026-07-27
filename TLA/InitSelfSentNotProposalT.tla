---------------------- MODULE InitSelfSentNotProposalT ----------------------
EXTENDS HPaxosPlusCal

LEMMA InitSelfSentNotProposalT == Init => SelfSentNotProposalInvT
<1> SUFFICES ASSUME Init PROVE SelfSentNotProposalInvT  OBVIOUS
<1>1. Msgs = {}  BY DEF Init
<1> QED BY <1>1 DEF SelfSentNotProposalInvT
====================================================================
