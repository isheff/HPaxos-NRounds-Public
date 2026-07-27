----------------------------- MODULE PairInCPairs -----------------------------
EXTENDS LearnerGraphConcrete

LEMMA PairInCPairs == ASSUME NEW x \in 1..4, NEW y \in 1..4 PROVE {x,y} \in CPairs
  <1>1. <<x,y>> \in CLrn \X CLrn BY DEF CLrn
  <1>2. {x,y} = {<<x,y>>[1], <<x,y>>[2]} OBVIOUS
  <1> QED BY <1>1, <1>2 DEF CPairs
=============================================================================
