--------------------------- MODULE CSafeStepDTSend ---------------------------
\* The step is enabled because it SENDS: the candidate is well formed, so the
\* step adds it to Msgs, and it has never been sent (CCandNotSent), so Msgs
\* genuinely grows and the angle-bracket disequality is met.  Whether the
\* acceptor already knew self[2] is irrelevant on this branch.
\*
\* EXTENDS is kept to the definition module: ExpandENABLED's witness search is
\* sensitive to ambient context, and this same BY fails with a heavier module
\* in scope.
EXTENDS CSafeStepDTDef, TLAPS

LEMMA CSafeStepDTSend ==
  ASSUME NEW self \in SafeAcceptors \X Messages,
         known_messages \in [SafeAcceptors -> SUBSET Messages],
         self[2] \in Msgs,
         TranExclusive(self[2]) \subseteq known_messages[self[1]],
         CWellFormed(CCand(self[1], self[2])),
         CCand(self[1], self[2]) \notin Msgs
  PROVE  ENABLED <<CSafeStepDT(self)>>_CVars
BY ExpandENABLED DEF CSafeStepDT, CVars
=============================================================================
