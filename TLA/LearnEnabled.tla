---------------------------- MODULE LearnEnabled ----------------------------
\* ExpandENABLED comes from TLAPS. Per the skill, the ENABLED recipe takes
\* NOTHING else in the BY -- adding Zenon/SMT breaks it.
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* ENABLED of the per-message learn action (deterministic send => trivial).
LEMMA LearnEnabled ==
  ASSUME NEW a \in SafeAcceptors, NEW x \in Msgs,
         TranExclusive(x) \subseteq known_messages[a],
         x \notin known_messages[a],
         known_messages \in [SafeAcceptors -> SUBSET Messages]
  PROVE  ENABLED <<safe_acceptor_receives_message(<<a, x>>)>>_vars
BY ExpandENABLED DEF safe_acceptor_receives_message, vars
====================================================================
