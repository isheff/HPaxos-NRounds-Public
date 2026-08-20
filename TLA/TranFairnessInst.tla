------------------------ MODULE TranFairnessInst ------------------------
EXTENDS HPaxosPlusCal

\* Same wall as NetworkAssumptionInst: backends cannot instantiate a \A-bound
\* WF_vars(...) fact at a literal tuple constructor via a bare DEF citation.
\* This lemma does the instantiation once, at a bound self, so call sites get
\* their literal-tuple instance via ordinary lemma application.
LEMMA TranFairnessInst ==
  ASSUME NEW pp, NEW self \in LiveAcceptors \times Tran(pp), TranFairness(pp)
  PROVE  WF_vars(safe_acceptor_receives_message(self))
BY DEF TranFairness
====================================================================
