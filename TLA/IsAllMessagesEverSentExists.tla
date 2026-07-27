--------------------- MODULE IsAllMessagesEverSentExists ---------------------
EXTENDS HPaxosPlusCal, TemporalComprehension

\* Witness existence for the "all messages ever sent" set, via TemporalComprehension
\* at DiaMem -- no temporal set-builder needed anywhere.
LEMMA IsAllMessagesEverSentExists == \E x : IsAllMessagesEverSent(x)
<1>1. \E x : \A mm : (mm \in x <=> (mm \in Messages /\ DiaMem(mm)))
  BY TemporalComprehension
<1> QED  BY <1>1 DEF IsAllMessagesEverSent, IAMESCond, DiaMem
====================================================================
