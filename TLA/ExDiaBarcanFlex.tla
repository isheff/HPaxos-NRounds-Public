--------------------------- MODULE ExDiaBarcanFlex ---------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* existential diamond-Barcan for a FLEXIBLE predicate S (Isa handles the
\* witness extraction from under <>; PTL cannot -- it is propositional).
\* This is a reusable lemma; its higher-order application (S := a compound
\* flexible predicate) goes through because S is matched from its HYPOTHESIS.
LEMMA ExDiaBarcanFlex ==
  ASSUME NEW TEMPORAL S(_), <>(\E z : S(z))
  PROVE  \E z : <>(S(z))
BY Isa
====================================================================
