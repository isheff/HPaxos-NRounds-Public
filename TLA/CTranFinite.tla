------------------------------ MODULE CTranFinite ------------------------------
EXTENDS MessageConcrete, CFields, CTranResolve, CMessagesSubMC, CFiniteTran

LEMMA CTranFinite == ASSUME MessageInterface = CMI PROVE TranFinite
<1> SUFFICES ASSUME NEW m \in Messages PROVE IsFiniteSet(Tran(m))  BY DEF TranFinite
<1>1. Messages = CMessages  BY CFields
<1>2. m \in CMessages  BY <1>1
<1>3. Tran(m) = CTran(m)  BY <1>2, CTranResolve
<1>4. m \in CMC  BY <1>2, CMessagesSubMC
<1>5. IsFiniteSet(CTran(m))  BY <1>4, CFiniteTran
<1> QED BY <1>3, <1>5
=============================================================================
