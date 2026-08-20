------------------------- MODULE RelevantLearnEnabled -------------------------
\* ENABLED of the LiveRelevant-restricted learn action.  Derived from
\* LearnEnabled's ENABLED of the unrestricted action: with both sides
\* ExpandENABLED'd, the hypothesis existential Skolemizes into exactly the
\* witnesses the goal existential needs, and the extra LiveRelevant conjunct
\* is unprimed, discharged from the LiveRelevant(x) hypothesis.
EXTENDS HPaxosPlusCal, LearnEnabled
LOCAL INSTANCE TLAPS

LEMMA RelevantLearnEnabled ==
  ASSUME NEW a \in SafeAcceptors, NEW x \in Msgs,
         TranExclusive(x) \subseteq known_messages[a],
         x \notin known_messages[a],
         known_messages \in [SafeAcceptors -> SUBSET Messages],
         LiveRelevant(x)
  PROVE  ENABLED <<relevant_receive(<<a, x>>)>>_vars
<1>en. ENABLED <<safe_acceptor_receives_message(<<a, x>>)>>_vars
  BY LearnEnabled
<1>imp. ENABLED <<safe_acceptor_receives_message(<<a, x>>)>>_vars
          => ENABLED <<relevant_receive(<<a, x>>)>>_vars
  BY ExpandENABLED
     DEF relevant_receive, safe_acceptor_receives_message, vars, LiveRelevant
<1> QED  BY <1>en, <1>imp
=============================================================================
