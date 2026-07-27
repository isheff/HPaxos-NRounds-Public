--------------------------- MODULE QdProperties ---------------------------
EXTENDS MessageInterface

\* What membership in Qd gives you (DEF Qd plus HasDepth's own signature
\* requirement).
LEMMA QdProperties ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW d \in Nat, d >= 1,
         NEW y \in Qd(alpha, x, d)
  PROVE /\ y \in TranExclusive(x)
        /\ B(y) = B(x)
        /\ Sig(y) \in Acceptors
        /\ HasDepth(alpha, y, d - 1)
<1>1. y \in TranExclusive(x) /\ B(x) = B(y) /\ HasDepth(alpha, y, d-1)  BY DEF Qd
<1>2. Sig(y) \in Acceptors  BY <1>1 DEF HasDepth
<1> QED BY <1>1, <1>2
====================================================================
