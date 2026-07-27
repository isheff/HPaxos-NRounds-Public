---------------------------- MODULE CIsTwoAResolve ----------------------------
EXTENDS MessageConcrete, CIsProposalResolve, CHasDepthResolve

\* IsTwoA (abstract) = CIsTwoA (concrete), on CMessages
LEMMA CIsTwoAResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE IsTwoA(x) = CIsTwoA(x)
<1>prop. IsProposal(x) = CIsProposal(x)  BY CIsProposalResolve
<1>1. IsTwoA(x) = (~IsProposal(x) /\ \E alpha \in Learners : HasDepth(alpha, x, 1))  BY DEF IsTwoA
<1>2. \A alpha \in Learners : HasDepth(alpha, x, 1) = CHasDepth(alpha, x, 1)
  <2> SUFFICES ASSUME NEW alpha \in Learners PROVE HasDepth(alpha, x, 1) = CHasDepth(alpha, x, 1)
    OBVIOUS
  <2>1. 1 \in Nat  OBVIOUS
  <2> QED BY <2>1, CHasDepthResolve
<1> QED BY <1>1, <1>2, <1>prop DEF CIsTwoA
=============================================================================
