----------------------------- MODULE SigSFiniteT -----------------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems

LEMMA SigSFiniteT == ASSUME NEW S, IsFiniteSet(S) PROVE IsFiniteSet(SigS(S))
BY FS_Image DEF SigS
====================================================================
