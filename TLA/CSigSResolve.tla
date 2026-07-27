----------------------------- MODULE CSigSResolve -----------------------------
EXTENDS MessageConcrete, CSigResolve

LEMMA CSigSResolve ==
  ASSUME MessageInterface = CMI, NEW S, S \subseteq CMessages
  PROVE SigS(S) = CSigS(S)
<1>1. SigS(S) = {Sig(xx) : xx \in S}  BY DEF SigS
<1>2. \A xx \in S : Sig(xx) = CSig(xx)  BY CSigResolve
<1> QED BY <1>1, <1>2 DEF CSigS
=============================================================================
