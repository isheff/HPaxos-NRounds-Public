------------------------ MODULE TemporalComprehension ------------------------
EXTENDS HPaxosPlusCal

\* Generic set-existence for a temporal predicate (ZF Separation schema).  Stated
\* and proved with NO set-builder, so SANY-clean: the comprehension
\* {mm \in S : P(mm)} would be a level error for temporal P at any syntactic
\* position, but the pure existence \E x : \A mm : (mm \in x <=> ...) is not.
LEMMA TemporalComprehension ==
  ASSUME NEW TEMPORAL P(_), NEW CONSTANT S
  PROVE  \E x : \A mm : (mm \in x <=> (mm \in S /\ P(mm)))
OBVIOUS
====================================================================
