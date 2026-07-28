--------------------------- MODULE CWitnessUnique ---------------------------
\* Any non-proposal message IS the record built from its own sender and
\* history.  All three fields are forced: the sender by CSig, the payload by
\* ~CIsProposal (CReply being a singleton), the priors by CFilterOut.
\* CMCShape supplies the record extensionality.
EXTENDS HPaxosPlusCalConcrete, CMCShape, CMessagesSubMC, CSelfInTran,
        CRefsIsMMax, TLAPS

LEMMA CWitnessUnique ==
  ASSUME NEW y \in CMessages, ~CIsProposal(y)
  PROVE  y = [sender  |-> CSig(y),
              payload |-> [type |-> "reply"],
              priors  |-> CMMax(CTranExcl(y))]
<1>mc. y \in CMC
  BY CMessagesSubMC
<1>shape. y \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
  BY <1>mc, CMCShape
<1>snd. y.sender = CSig(y)
  BY DEF CSig
<1>pay. y.payload = [type |-> "reply"]
  <2>1. y.payload \in CPayload
    BY <1>shape
  <2>2. y.payload \notin CProposal
    BY DEF CIsProposal
  <2>3. y.payload \in CReply
    BY <2>1, <2>2 DEF CPayload
  <2> QED
    BY <2>3 DEF CReply
<1>pri. y.priors = CMMax(CTranExcl(y))
  <2>1. y \in CTran(y)
    BY <1>mc, CSelfInTran
  <2>2. CWellFormed(y)
    BY <2>1 DEF CMessages
  <2>3. y.priors = CRefs(y)
    BY <2>2 DEF CWellFormed, CFilterOut
  <2> QED
    BY <2>3, CRefsIsMMax
<1> QED
  BY <1>shape, <1>snd, <1>pay, <1>pri
=============================================================================
