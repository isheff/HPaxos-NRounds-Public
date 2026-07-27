------------------------------ MODULE CflId ------------------------------
EXTENDS MessageInterface, CombinedFreshQdLrnsIdRec

LEMMA CflId ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic, NEW p \in Messages
  PROVE CombinedFreshQdLrnsId(p).id = p
<1>1. CombinedFreshQdLrnsId(p)
        = CombinedFreshQdLrnsIdR(p, {CombinedFreshQdLrnsId(q) : q \in TranExclusive(p)})
  BY CombinedFreshQdLrnsIdRec
<1> QED BY <1>1 DEF CombinedFreshQdLrnsIdR
====================================================================
