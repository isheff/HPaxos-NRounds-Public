--------------------------- MODULE CSafeGuardsIdentical ---------------------------
\* The concrete and abstract safe-acceptor actions carry the SAME two guard
\* conjuncts, syntactically.  Each is then total in its primed variables once
\* the guard holds -- every one is fixed by an equation, with no residual
\* choice -- so neither can be enabled where the other is not, and the extra
\* conjunct recent_messages' = CRecentUpdate(s,x) cannot block a step,
\* CRecentUpdate being a closed term.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CSafeGuardsIdentical ==
  ASSUME NEW s, NEW x
  PROVE  /\ CSafeStep(<<s, x>>)
              => (x \in Msgs /\ TranExclusive(x) \subseteq known_messages[s])
         /\ safe_acceptor_receives_message(<<s, x>>)
              => (x \in Msgs /\ TranExclusive(x) \subseteq known_messages[s])
BY DEF CSafeStep, safe_acceptor_receives_message
=============================================================================
