------------------------- MODULE CSafeStepDTEnabled -------------------------
\* The normal form enables the real action.  CSafeStepDT is CSafeStep with the
\* IF pushed into a disjunction, so any transition of the one is a transition
\* of the other; with both ENABLEDs expanded, the hypothesis existential
\* Skolemizes into exactly the witnesses the goal existential needs.
EXTENDS CSafeStepDTDef, TLAPS

LEMMA CSafeStepDTEnabled ==
  ASSUME NEW self \in SafeAcceptors \X Messages,
         ENABLED <<CSafeStepDT(self)>>_CVars
  PROVE  ENABLED <<CSafeStep(self)>>_CVars
BY ExpandENABLED DEF CSafeStepDT, CSafeStep, CVars, CCand, CRM
=============================================================================
