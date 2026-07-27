------------------------ MODULE CTypeOKMessageInterface ------------------------
EXTENDS MessageConcrete, CFields, CMessageTranClosed, CMessagesSubMC, CMCShape

LEMMA CTypeOKMessageInterface == ASSUME MessageInterface = CMI PROVE TypeOKMessageInterface
<1>msg. Messages = CMessages  BY CFields
<1>prop. Proposals = CProposals  BY CFields
<1>send. Senders = CSenders  BY CFields
<1>1. MessageInterface.tran \in [Messages -> SUBSET Messages]
  <2>1. MessageInterface.tran = CTranField  BY DEF CMI
  <2>2. CTranField \in [CMessages -> SUBSET CMessages]
    <3> SUFFICES ASSUME NEW m \in CMessages PROVE CTranField[m] \in SUBSET CMessages
      BY DEF CTranField
    <3>1. CTranField[m] = CTranExcl(m)  BY DEF CTranField
    <3>2. CTranExcl(m) \subseteq CTran(m)  BY DEF CTranExcl
    <3>3. CTran(m) \subseteq CMessages  BY CMessageTranClosed
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>1, <2>2, <1>msg
<1>2. MessageInterface.sig \in [Messages -> Senders]
  <2>1. MessageInterface.sig = CSigField  BY DEF CMI
  <2>2. CSigField \in [CMessages -> CSenders]
    <3> SUFFICES ASSUME NEW m \in CMessages PROVE CSigField[m] \in CSenders
      BY DEF CSigField
    <3>1. CSigField[m] = CSig(m)  BY DEF CSigField
    <3>2. m \in CMC  BY CMessagesSubMC
    <3>3. m \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]  BY <3>2, CMCShape
    <3>4. CSig(m) = m.sender  BY DEF CSig
    <3> QED BY <3>1, <3>3, <3>4
  <2> QED BY <2>1, <2>2, <1>msg, <1>send
<1>3. Proposals \subseteq Messages  BY <1>msg, <1>prop DEF CProposals
<1>4. MessageInterface.proposalbal \in [Proposals -> Ballots]
  <2>1. MessageInterface.proposalbal = CProposalBalField  BY DEF CMI
  <2>2. CProposalBalField \in [CProposals -> Ballots]
    <3> SUFFICES ASSUME NEW p \in CProposals PROVE CProposalBalField[p] \in Ballots
      BY DEF CProposalBalField
    <3>1. CProposalBalField[p] = p.payload.ballot  BY DEF CProposalBalField
    <3>2. p.payload \in CProposal  BY DEF CProposals, CIsProposal
    <3>3. p.payload.ballot \in Ballots  BY <3>2 DEF CProposal
    <3> QED BY <3>1, <3>3
  <2> QED BY <2>1, <2>2, <1>prop
<1> QED BY <1>1, <1>2, <1>3, <1>4 DEF TypeOKMessageInterface
=============================================================================
