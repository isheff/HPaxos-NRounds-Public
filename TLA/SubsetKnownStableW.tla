------------------------- MODULE SubsetKnownStableW -------------------------
\* Thin op-wrapper over the (already proven) temporal lemma, identity citation.
\* The wrapper exists so the conclusion is an opaque operator application,
\* which is what makes non-identity instantiation possible at call sites.
EXTENDS HPaxosPlusCal, SubsetKnownStable

LEMMA SubsetKnownStableW == ASSUME NEW a \in SafeAcceptors, NEW SS PROVE SKSop(a, SS)
BY SubsetKnownStable DEF SKSop
====================================================================
