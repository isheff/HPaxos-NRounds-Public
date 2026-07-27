------------------------ MODULE EqFromLeGeBallotsT ------------------------
EXTENDS HPaxosPlusCal

LEMMA EqFromLeGeBallotsT ==
  ASSUME NEW p \in Ballots, NEW q \in Ballots, p <= q, p >= q
  PROVE p = q
BY DEF Ballots
====================================================================
