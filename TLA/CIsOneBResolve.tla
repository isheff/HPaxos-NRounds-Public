---------------------------- MODULE CIsOneBResolve ----------------------------
EXTENDS MessageConcrete, CIsProposalResolve, CTranResolve,
        CMessageTranClosed, CBResolve

LEMMA CIsOneBResolve ==
  ASSUME MessageInterface = CMI, NEW x \in CMessages
  PROVE IsOneB(x) = CIsOneB(x)
<1>prop. IsProposal(x) = CIsProposal(x)  BY CIsProposalResolve
<1>1. IsOneB(x) = (~IsProposal(x) /\ Cardinality({y \in Tran(x) : B(y) = B(x)}) = 2)  BY DEF IsOneB
<1>2. Tran(x) = CTran(x)  BY CTranResolve
<1>3. \A y \in CTran(x) : y \in CMessages  BY CMessageTranClosed
<1>4. \A y \in CTran(x) : B(y) = CB(y)  BY <1>3, CBResolve
<1>5. B(x) = CB(x)  BY CBResolve
<1>6. {y \in Tran(x) : B(y) = B(x)} = {y \in CTran(x) : CB(y) = CB(x)}  BY <1>2, <1>4, <1>5
<1> QED BY <1>1, <1>6, <1>prop DEF CIsOneB
=============================================================================
