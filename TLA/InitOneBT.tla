----------------------------- MODULE InitOneBT -----------------------------
EXTENDS HPaxosPlusCal

LEMMA InitOneBT == Init => OneBInvariantT
<1> SUFFICES ASSUME Init PROVE OneBInvariantT  OBVIOUS
<1>1. known_messages = [s \in SafeAcceptors |-> {}]  BY DEF Init
<1> QED BY <1>1 DEF OneBInvariantT
====================================================================
