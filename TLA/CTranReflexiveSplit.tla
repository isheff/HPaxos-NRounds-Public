-------------------------- MODULE CTranReflexiveSplit --------------------------
EXTENDS MessageConcrete, CSelfInTran

LEMMA CTranReflexiveSplit == ASSUME NEW m \in CMC PROVE CTran(m) = {m} \cup CTranExcl(m)
BY CSelfInTran DEF CTranExcl
=============================================================================
