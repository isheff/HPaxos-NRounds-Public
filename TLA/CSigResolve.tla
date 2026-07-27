------------------------------ MODULE CSigResolve ------------------------------
EXTENDS MessageConcrete

LEMMA CSigResolve == ASSUME MessageInterface = CMI, NEW m \in CMessages
  PROVE Sig(m) = CSig(m)
<1>1. Sig(m) = MessageInterface.sig[m]  BY DEF Sig
<1>2. MessageInterface.sig[m] = CSig(m)  BY DEF CMI, CSigField
<1> QED BY <1>1, <1>2
=============================================================================
