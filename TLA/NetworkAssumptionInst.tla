----------------------- MODULE NetworkAssumptionInst -----------------------
EXTENDS HPaxosPlusCal

\* Backends cannot instantiate a \A-bound WF_vars(...) fact at a literal tuple
\* constructor (e.g. WF_vars(F(<<a, x>>))) via a bare `DEF NetworkAssumption`
\* citation -- congruence through WF_vars doesn't fire on syntactically-built
\* tuples, only on an already-bound pair variable.  This lemma does the
\* instantiation once, at a bound `self`, so call sites can get their literal-
\* tuple instance via ordinary lemma application (which unifies fine) instead.
LEMMA NetworkAssumptionInst ==
  ASSUME NEW self \in LiveAcceptors \times Messages, NetworkAssumption
  PROVE  WF_vars(relevant_receive(self))
BY DEF NetworkAssumption
====================================================================
