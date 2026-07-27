----------------------------- MODULE LeFromEqT -----------------------------
EXTENDS HPaxosPlusCal

LEMMA LeFromEqT == ASSUME NEW p \in Ballots, NEW q \in Ballots, p = q PROVE p <= q
BY DEF Ballots
====================================================================
