-------------------------- MODULE DiaBoxAtomContra --------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* s eventually caught yet never caught -> FALSE.  Ordinary param s so it
\* applies by matching; PTL runs in a clean (non-temporal-hyp) context.  Both
\* facts use the SAME atom (s \in CaughtS(Msgs)) so PTL coalescing connects
\* them (it does NOT relate \notin to ~ \in).
LEMMA DiaBoxAtomContra ==
  ASSUME NEW s, <>(s \in CaughtS(Msgs)), [](~(s \in CaughtS(Msgs)))
  PROVE  FALSE
BY PTL
====================================================================
