------------------------------ MODULE InitAuxT ------------------------------
EXTENDS HPaxosPlusCal,
        InitInv, InitKnownClosureT, InitSelfSentT, InitSelfSentNotProposalT, InitChain

LEMMA InitAuxT == Init => AuxT
BY InitInv, InitKnownClosureT, InitSelfSentT, InitSelfSentNotProposalT, InitChain DEF AuxT
====================================================================
