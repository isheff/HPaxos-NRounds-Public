--------------------------- MODULE CRefsIsMMax ---------------------------
\* CRefs is exactly the maximal antichain of a message's strict history.
\* Purely propositional once CTranExcl is unfolded: CRefs's
\* "y = x \/ x \notin CTran(y)" and CMMax's "x \notin CTranExcl(y)" are the
\* same condition.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CRefsIsMMax == \A m : CRefs(m) = CMMax(CTranExcl(m))
BY DEF CRefs, CMMax, CTranExcl
=============================================================================
