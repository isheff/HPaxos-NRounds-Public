-------------------------- MODULE CByzStepEnabled --------------------------
\* ENABLED transfers for a Byzantine sender, with nothing assumed at all.
\*
\* The two actions offer the SAME set of messages to send -- CByzStep is
\* HPaxosPlusCal's byz verbatim, plus UNCHANGED recent_messages -- and neither
\* touches known_messages.  So a state change under either is a change in Msgs,
\* certified by the same witness y.  With both ENABLEDs expanded, the
\* hypothesis existential Skolemizes into exactly the witness the goal
\* existential needs; freezing recent_messages cannot block a step.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CByzStepEnabled ==
  ASSUME NEW self \in ByzSenders,
         ENABLED <<byz(self)>>_vars
  PROVE  ENABLED <<CByzStep(self)>>_CVars
BY ExpandENABLED DEF byz, CByzStep, vars, CVars
=============================================================================
