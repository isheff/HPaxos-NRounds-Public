--------------------------- MODULE CByzEquiv ---------------------------
\* Byzantine senders are unchanged from HPaxosPlusCal: syntactically the same
\* action, with the concrete one additionally freezing recent_messages.
\* Nothing about the message interface is needed.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CByzEquiv ==
  ASSUME NEW self \in ByzSenders
  PROVE  CByzStep(self) <=> (byz(self) /\ UNCHANGED recent_messages)
BY DEF CByzStep, byz
=============================================================================
