--------------------------- MODULE CHasDepthResolve ---------------------------
EXTENDS MessageConcrete, CCflResolve, CSigResolve, CIsOneBResolve,
        CMessagesSubMC, CQdSubset, CMessageTranClosed, CSigSResolve

LEMMA CHasDepthResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages, NEW alpha \in Learners, NEW dd \in Nat
  PROVE HasDepth(alpha, x, dd) = CHasDepth(alpha, x, dd)
<1>1. CombinedFreshQdLrnsId(x) = CCfl(x)  BY CCflResolve
<1>sx. Sig(x) = CSig(x)  BY CSigResolve
<1>2. CASE dd = 0
  <2>1. HasDepth(alpha, x, dd) = (Sig(x) \in Acceptors /\ IsOneB(x) /\ CombinedFreshQdLrnsId(x).fresh[alpha])
    BY <1>2 DEF HasDepth
  <2>2. CHasDepth(alpha, x, dd) = (CSig(x) \in Acceptors /\ CIsOneB(x) /\ CCfl(x).fresh[alpha])
    BY <1>2 DEF CHasDepth
  <2>3. IsOneB(x) = CIsOneB(x)  BY CIsOneBResolve
  <2> QED BY <2>1, <2>2, <2>3, <1>1, <1>sx
<1>3. CASE dd # 0
  <2>1. HasDepth(alpha, x, dd) = (Sig(x) \in Acceptors /\ SigS(CombinedFreshQdLrnsId(x).qd[<<alpha, dd>>]) \in Quorums(alpha))
    BY <1>3 DEF HasDepth
  <2>2. CHasDepth(alpha, x, dd) = (CSig(x) \in Acceptors /\ CSigS(CCfl(x).qd[<<alpha, dd>>]) \in Quorums(alpha))
    BY <1>3 DEF CHasDepth
  <2>3. x \in CMC  BY CMessagesSubMC
  <2>4. CCfl(x).qd[<<alpha, dd>>] \subseteq CTranExcl(x)  BY <2>3, CQdSubset
  <2>5. CTranExcl(x) \subseteq CMessages
    <3> SUFFICES ASSUME NEW z \in CTranExcl(x) PROVE z \in CMessages  OBVIOUS
    <3>1. z \in CTran(x)  BY DEF CTranExcl
    <3> QED BY <3>1, CMessageTranClosed
  <2>6. CCfl(x).qd[<<alpha, dd>>] \subseteq CMessages  BY <2>4, <2>5
  <2>7. SigS(CCfl(x).qd[<<alpha, dd>>]) = CSigS(CCfl(x).qd[<<alpha, dd>>])  BY <2>6, CSigSResolve
  <2> QED BY <2>1, <2>2, <2>7, <1>1, <1>sx
<1> QED BY <1>2, <1>3
=============================================================================
