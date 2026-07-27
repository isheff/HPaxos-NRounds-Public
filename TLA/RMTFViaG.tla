---------------------------- MODULE RMTFViaG ----------------------------
\* Pure definition-unfolding: only MessageInterface definitions are involved
\* (RecursiveMessageTranFunc, GFunMI, TranExclusive, Cardinality, Tran).
EXTENDS MessageInterface

\* Bridge: the file's RecursiveMessageTranFunc equals GFunMI at the message's level.
LEMMA RMTFViaG ==
  ASSUME NEW F(_,_), NEW z
  PROVE RecursiveMessageTranFunc(F, z) = GFunMI(F, TranExclusive)[Cardinality(Tran(z))][z]
BY DEF RecursiveMessageTranFunc, GFunMI
====================================================================
