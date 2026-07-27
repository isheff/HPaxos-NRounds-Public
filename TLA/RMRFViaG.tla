---------------------------- MODULE RMRFViaG ----------------------------
\* Pure definition-unfolding: only MessageInterface definitions are involved
\* (RecursiveMessageRefsFunc, GFunMI, Refs, Cardinality, Tran).
EXTENDS MessageInterface

\* Bridge: the file's RecursiveMessageRefsFunc equals GFunMI at the message's level.
LEMMA RMRFViaG ==
  ASSUME NEW F(_,_), NEW z
  PROVE RecursiveMessageRefsFunc(F, z) = GFunMI(F, Refs)[Cardinality(Tran(z))][z]
BY DEF RecursiveMessageRefsFunc, GFunMI
====================================================================
