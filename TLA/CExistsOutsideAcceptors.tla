----------------------- MODULE CExistsOutsideAcceptors -----------------------
EXTENDS MessageConcrete

LEMMA CExistsOutsideAcceptors == \E x : x \notin Acceptors
<1> SUFFICES ASSUME \A x : x \in Acceptors
             PROVE FALSE
  OBVIOUS
<1>univ. \A x : x \in Acceptors  OBVIOUS
<1> DEFINE R == {y \in Acceptors : y \notin y}
<1>1. R \in Acceptors  BY <1>univ
<1>2. R \in R <=> (R \in Acceptors /\ R \notin R)  OBVIOUS
<1> QED BY <1>1, <1>2
=============================================================================
