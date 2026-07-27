-------------------------------- MODULE CCflId --------------------------------
EXTENDS MessageConcrete, CCflRec

LEMMA CCflId == ASSUME NEW y \in CMC PROVE CCfl(y).id = y
BY CCflRec DEF CCflR
=============================================================================
