-------------------------- MODULE CRelWFTransferAt --------------------------
\* CWFTransferAt for the LiveRelevant-restricted actions: if the concrete
\* spec is weakly fair to a live acceptor's RESTRICTED learn step, the
\* abstract spec is weakly fair to the restricted abstract step.
\*
\* Same PTL shape as CWFTransferAt.  The two boxed premises reduce to the
\* unrestricted ones (CSafeStepEnabled / CSafeStepAngle): the LiveRelevant
\* conjunct is an unprimed state predicate over the SHARED variables, so it
\* factors out of both ENABLEDs (ExpandENABLED, witness passed through
\* unchanged) and carries across the angle-bracket projection.
\*
\* CSpec is kept in the GOAL rather than the hypotheses on purpose: a raw
\* temporal hypothesis in scope silently disables PTL's necessitation.
EXTENDS HPaxosPlusCalConcrete, CSafeStepEnabled, CSafeStepAngle,
        CJointHolds, TLAPS

LEMMA CRelWFTransferAt ==
  ASSUME ConcreteMessageInterface, AcceptorsAssumptions,
         NEW self \in LiveAcceptors \X Messages
  PROVE  CSpec /\ WF_CVars(CRelevantStep(self))
           => WF_vars(relevant_receive(self))
<1>sa. self[1] \in SafeAcceptors /\ self[2] \in Messages
         /\ self \in SafeAcceptors \X Messages
  <2>1. self[1] \in LiveAcceptors /\ self[2] \in Messages
          /\ self = <<self[1], self[2]>>
    OBVIOUS
  <2>2. self[1] \in SafeAcceptors
    BY <2>1 DEF AcceptorsAssumptions, LiveAcceptorsAssumption
  <2> QED
    BY <2>1, <2>2
<1>saa. SafeAcceptorsAssumption
  BY DEF AcceptorsAssumptions
<1>en. CJoint => (ENABLED <<relevant_receive(self)>>_vars
                    => ENABLED <<CRelevantStep(self)>>_CVars)
  <2>fa. ENABLED <<relevant_receive(self)>>_vars
           => LiveRelevant(self[2])
              /\ ENABLED <<safe_acceptor_receives_message(self)>>_vars
    BY ExpandENABLED
       DEF relevant_receive, safe_acceptor_receives_message, vars, LiveRelevant
  <2>fc. LiveRelevant(self[2]) /\ ENABLED <<CSafeStep(self)>>_CVars
           => ENABLED <<CRelevantStep(self)>>_CVars
    BY ExpandENABLED DEF CRelevantStep, CSafeStep, CVars, LiveRelevant
  <2>tr. CJoint /\ ENABLED <<safe_acceptor_receives_message(self)>>_vars
           => ENABLED <<CSafeStep(self)>>_CVars
    BY <1>sa, <1>saa, CSafeStepEnabled
  <2> QED  BY <2>fa, <2>fc, <2>tr
<1>mv. CJoint /\ <<CRelevantStep(self)>>_CVars
         => <<relevant_receive(self)>>_vars
  <2>1. CJoint /\ <<CSafeStep(self)>>_CVars
          => <<safe_acceptor_receives_message(self)>>_vars
    BY <1>sa, <1>saa, CSafeStepAngle
  <2> QED  BY <2>1 DEF CRelevantStep, relevant_receive
<1>jt. CSpec => []CJoint
  BY <1>saa, CJointHolds
<1>ben. CSpec => [](ENABLED <<relevant_receive(self)>>_vars
                      => ENABLED <<CRelevantStep(self)>>_CVars)
  BY <1>en, <1>jt, PTL
<1>bmv. CSpec => BoxAct(<<CRelevantStep(self)>>_CVars
                          => <<relevant_receive(self)>>_vars)
  BY <1>mv, <1>jt, PTL DEF BoxAct
<1> QED
  BY <1>ben, <1>bmv, PTL DEF BoxAct
=============================================================================
