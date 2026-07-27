------------------------------ MODULE CConResolve ------------------------------
EXTENDS MessageConcrete, CCaughtResolve

LEMMA CConResolve ==
  ASSUME MessageInterface = CMI, NEW alpha \in Learners, NEW x \in CMessages
  PROVE Con(alpha, x) = CCon(alpha, x)
<1>1. Con(alpha, x) = ConFromCaught(alpha, Caught(x))  BY DEF Con
<1>2. Caught(x) = CCaughtS(CTran(x))  BY CCaughtResolve
<1> QED BY <1>1, <1>2 DEF CCon, CCaught
=============================================================================
