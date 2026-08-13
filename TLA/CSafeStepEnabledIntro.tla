----------------------- MODULE CSafeStepEnabledIntro -----------------------
\* Introducing ENABLED for the CONCRETE step.
\*
\* CSafeStep is TOTAL in its primed variables once the guards hold -- Msgs',
\* known_messages' and recent_messages' are each fixed by an equation, with no
\* residual choice -- so the guards alone already give ENABLED CSafeStep.  The
\* ANGLE-bracket form asks one thing more: that the state actually MOVES.  The
\* hypothesis below is exactly the two ways it can.  Either the candidate is
\* well formed and unsent, and Msgs grows (CSafeStepDTSend); or it is not well
\* formed but self[2] is new, and known_messages grows (CSafeStepDTLearn).
\*
\* No ExpandENABLED here: the two branch lemmas and the normal-form transfer
\* are cited as ordinary facts, so the ENABLED atoms stay opaque and the case
\* analysis costs nothing.
EXTENDS CSafeStepDTEnabled, CSafeStepDTSend, CSafeStepDTLearn, TLAPS

LEMMA CSafeStepEnabledIntro ==
  ASSUME NEW self \in SafeAcceptors \X Messages,
         known_messages \in [SafeAcceptors -> SUBSET Messages],
         self[2] \in Msgs,
         TranExclusive(self[2]) \subseteq known_messages[self[1]],
         \/ (/\ ~CWellFormed(CCand(self[1], self[2]))
             /\ self[2] \notin known_messages[self[1]])
         \/ (/\ CWellFormed(CCand(self[1], self[2]))
             /\ CCand(self[1], self[2]) \notin Msgs)
  PROVE  ENABLED <<CSafeStep(self)>>_CVars
<1>d. ENABLED <<CSafeStepDT(self)>>_CVars
  <2>1. CASE ~CWellFormed(CCand(self[1], self[2]))
              /\ self[2] \notin known_messages[self[1]]
    BY <2>1, CSafeStepDTLearn
  <2>2. CASE CWellFormed(CCand(self[1], self[2]))
              /\ CCand(self[1], self[2]) \notin Msgs
    BY <2>2, CSafeStepDTSend
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>d, CSafeStepDTEnabled
=============================================================================
