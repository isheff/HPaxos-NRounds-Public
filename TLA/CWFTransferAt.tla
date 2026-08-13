--------------------------- MODULE CWFTransferAt ---------------------------
\* Weak fairness transfers, one process at a time: if the concrete spec is
\* weakly fair to a live acceptor's learn step, the abstract spec is too.
\*
\* This is WF's own shape, discharged by PTL from two boxed premises:
\*
\*   - []( ENABLED <<abstract>>_vars => ENABLED <<concrete>>_CVars )
\*     so a continuously-enabled abstract step keeps the concrete one enabled
\*     and the concrete fairness obligation actually fires  (CSafeStepEnabled);
\*   - []( <<concrete>>_CVars => <<abstract>>_vars )
\*     so what fires counts as abstract progress and is not a stutter for
\*     HPaxosPlusCal  (CSafeStepAngle).
\*
\* Both are state/action facts about CJoint states, lifted to [] by CJointHolds
\* -- the whole temporal content is that one INV1 step plus PTL's native
\* handling of WF_.  BoxAct is HPaxosPlusCal's level-laundering wrapper, needed
\* because the second premise boxes an ACTION.
\*
\* CSpec is kept in the GOAL rather than the hypotheses on purpose: a raw
\* temporal hypothesis in scope silently disables PTL's necessitation.
EXTENDS HPaxosPlusCalConcrete, CSafeStepEnabled, CSafeStepAngle,
        CJointHolds, TLAPS

LEMMA CWFTransferAt ==
  ASSUME ConcreteMessageInterface, AcceptorsAssumptions,
         NEW self \in LiveAcceptors \X Messages
  PROVE  CSpec /\ WF_CVars(CSafeStep(self))
           => WF_vars(safe_acceptor_receives_message(self))
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
<1>en. CJoint => (ENABLED <<safe_acceptor_receives_message(self)>>_vars
                    => ENABLED <<CSafeStep(self)>>_CVars)
  BY <1>sa, <1>saa, CSafeStepEnabled
<1>mv. CJoint /\ <<CSafeStep(self)>>_CVars
         => <<safe_acceptor_receives_message(self)>>_vars
  BY <1>sa, <1>saa, CSafeStepAngle
<1>jt. CSpec => []CJoint
  BY <1>saa, CJointHolds
<1>ben. CSpec => [](ENABLED <<safe_acceptor_receives_message(self)>>_vars
                      => ENABLED <<CSafeStep(self)>>_CVars)
  BY <1>en, <1>jt, PTL
<1>bmv. CSpec => BoxAct(<<CSafeStep(self)>>_CVars
                          => <<safe_acceptor_receives_message(self)>>_vars)
  BY <1>mv, <1>jt, PTL DEF BoxAct
<1> QED
  BY <1>ben, <1>bmv, PTL DEF BoxAct
=============================================================================
