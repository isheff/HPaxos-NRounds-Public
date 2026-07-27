------------------------------ MODULE CSelfInTran ------------------------------
EXTENDS MessageConcrete, CTranRec

LEMMA CSelfInTran == ASSUME NEW m \in CMC PROVE m \in CTran(m)
BY CTranRec
=============================================================================
