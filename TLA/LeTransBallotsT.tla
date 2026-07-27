-------------------------- MODULE LeTransBallotsT --------------------------
EXTENDS HPaxosPlusCal

LEMMA LeTransBallotsT ==
  ASSUME NEW p \in Ballots, NEW q \in Ballots, NEW r \in Ballots, p <= q, q <= r
  PROVE p <= r
BY DEF Ballots
====================================================================
