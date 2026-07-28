--------------------------- MODULE CInitEquiv ---------------------------
\* The concrete initial predicate is the abstract one plus the initial value of
\* the extra variable.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CInitEquiv ==
  CInit <=> (Init /\ recent_messages = [s \in SafeAcceptors |-> {}])
BY DEF CInit, Init
=============================================================================
