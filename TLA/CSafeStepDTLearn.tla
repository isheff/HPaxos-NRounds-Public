-------------------------- MODULE CSafeStepDTLearn --------------------------
\* The step is enabled because it LEARNS: the candidate is not well formed, so
\* nothing is sent and recent_messages only writes back CRM -- but self[2] is
\* new to the acceptor, so known_messages[self[1]] grows and the angle-bracket
\* disequality is met there.
\*
\* EXTENDS is kept to the definition module, for the same context-sensitivity
\* reason as CSafeStepDTSend.
EXTENDS CSafeStepDTDef, TLAPS

LEMMA CSafeStepDTLearn ==
  ASSUME NEW self \in SafeAcceptors \X Messages,
         known_messages \in [SafeAcceptors -> SUBSET Messages],
         self[2] \in Msgs,
         TranExclusive(self[2]) \subseteq known_messages[self[1]],
         self[2] \notin known_messages[self[1]],
         ~CWellFormed(CCand(self[1], self[2]))
  PROVE  ENABLED <<CSafeStepDT(self)>>_CVars
BY ExpandENABLED DEF CSafeStepDT, CVars
=============================================================================
