--------------------- MODULE IsAllMessagesEverKnownExists ---------------------
EXTENDS HPaxosPlusCal, TemporalComprehension

\* Witness existence for the "all messages ever known to a live acceptor" set,
\* via TemporalComprehension at DiaKTL -- no temporal set-builder needed
\* anywhere.
LEMMA IsAllMessagesEverKnownExists == \E x : IsAllMessagesEverKnown(x)
<1>1. \E x : \A mm : (mm \in x <=> (mm \in Messages /\ DiaKTL(mm)))
  BY TemporalComprehension
<1> QED  BY <1>1 DEF IsAllMessagesEverKnown, IAMEKCond, DiaKTL
====================================================================
