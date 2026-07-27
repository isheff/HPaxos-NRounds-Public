---------------------------- MODULE TranAntisym ----------------------------
EXTENDS MessageInterface

\* Tran is antisymmetric. MI has no WellFormed/Message split like HPaxos.tla, so
\* this is derived directly from TranAcyclic rather than needing a separate axiom.
LEMMA TranAntisym ==
  ASSUME TranAcyclic, NEW p \in Messages, NEW q \in Messages,
         p \in Tran(q), q \in Tran(p)
  PROVE p = q
<1> SUFFICES ASSUME p # q PROVE FALSE  OBVIOUS
<1>1. p \in TranExclusive(q)  BY DEF TranExclusive
<1> QED BY <1>1 DEF TranAcyclic
====================================================================
