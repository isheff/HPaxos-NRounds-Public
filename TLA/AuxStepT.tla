------------------------------ MODULE AuxStepT ------------------------------
EXTENDS HPaxosPlusCal,
        InvStep, KnownClosureStepT, SelfSentStepT, SelfSentNotProposalStepT, ChainStep

LEMMA AuxStepT == AuxT /\ [Next]_vars => AuxT'
<1> SUFFICES ASSUME AuxT, [Next]_vars PROVE AuxT'  OBVIOUS
<1>i. Inv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ SelfSentNotProposalInvT /\
      SafeAcceptorChainInv
  BY DEF AuxT
<1>a. Inv'  BY <1>i, InvStep
<1>b. KnownTranClosureInvT'  BY <1>i, KnownClosureStepT
<1>c. SelfSentBoundedInvT'  BY <1>i, SelfSentStepT
<1>d. SelfSentNotProposalInvT'  BY <1>i, SelfSentNotProposalStepT
<1>e. SafeAcceptorChainInv'  BY <1>i, ChainStep
<1> QED BY <1>a, <1>b, <1>c, <1>d, <1>e DEF AuxT
====================================================================
