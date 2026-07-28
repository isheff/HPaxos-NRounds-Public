--------------------------- MODULE CTranClosureAdd ---------------------------
\* Adding one element whose strict history is already inside a Tran-closed set
\* keeps it Tran-closed.  This is what makes known_messages[s] \cup {x} still
\* Tran-closed after a receive.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CTranClosureAdd ==
  ASSUME NEW A, NEW x, TranExclusive(x) \subseteq A, TranClosure(A) = A
  PROVE  TranClosure(A \cup {x}) = A \cup {x}
<1>1. TranClosure(A \cup {x}) = TranClosure(A) \cup Tran(x)
  BY DEF TranClosure
<1>2. Tran(x) = {x} \cup TranExclusive(x)
  BY DEF Tran, TranExclusive
<1> QED
  BY <1>1, <1>2
=============================================================================
