------------------------------- MODULE CVResolve -------------------------------
EXTENDS MessageConcrete, CBResolve

LEMMA CVResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE V(x) = CV(x)
<1>1. V(x) = BalToVal(B(x))  BY DEF V
<1>2. B(x) = CB(x)  BY CBResolve
<1> QED BY <1>1, <1>2 DEF CV
=============================================================================
