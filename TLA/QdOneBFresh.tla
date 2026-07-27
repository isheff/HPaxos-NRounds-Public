--------------------------- MODULE QdOneBFresh ---------------------------
EXTENDS MessageInterface, TranSubMessages, HasDepthDef

\* Depth-1 quorum members are fresh OneBs (HasDepthDef at d = 0).
LEMMA QdOneBFresh ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, TranAcyclic,
         NEW alpha \in Learners, NEW x \in Messages,
         NEW y \in Qd(alpha, x, 1)
  PROVE IsOneB(y) /\ Fresh(alpha, y) /\ Sig(y) \in Acceptors
<1>1. y \in TranExclusive(x) /\ B(x) = B(y) /\ HasDepth(alpha, y, 0)  BY DEF Qd
<1>yM. y \in Messages
  <2>1. y \in Tran(x)  BY <1>1 DEF TranExclusive
  <2> QED BY <2>1, TranSubMessages
<1>z. 0 \in Nat  OBVIOUS
<1>2. HasDepth(alpha, y, 0) =
        (/\ Sig(y) \in Acceptors
         /\ IF 0 = 0 THEN (IsOneB(y) /\ Fresh(alpha, y))
                     ELSE SigS(Qd(alpha, y, 0)) \in Quorums(alpha))
  BY <1>yM, <1>z, HasDepthDef
<1> QED BY <1>1, <1>2
====================================================================
