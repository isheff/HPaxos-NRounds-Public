-------------------------- MODULE OneBInvariantEqT --------------------------
EXTENDS HPaxosPlusCal

LEMMA OneBInvariantEqT == OneBInvariantT => OneBInvariant
BY DEF OneBInvariantT, OneBInvariant
====================================================================
