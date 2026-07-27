---------------------------- MODULE CaughtSMonoT ----------------------------
EXTENDS HPaxosPlusCal

LEMMA CaughtSMonoT ==
  ASSUME NEW M1, NEW M2, M1 \subseteq M2
  PROVE CaughtS(M1) \subseteq CaughtS(M2)
BY DEF CaughtS
====================================================================
