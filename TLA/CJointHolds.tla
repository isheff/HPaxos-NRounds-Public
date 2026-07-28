--------------------------- MODULE CJointHolds ---------------------------
\* The joint invariant holds throughout the concrete spec.  Standard INV1
\* assembly: initial case, step case, PTL.
EXTENDS HPaxosPlusCalConcrete, CJointInit, CJointSafeStep, CJointByzStep,
        CJointStutter, TLAPS

LEMMA CJointHolds ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption
  PROVE  CSpec => []CJoint
<1>1. CInit => CJoint
  BY CJointInit
<1>2. CJoint /\ [CNext]_CVars => CJoint'
  <2> SUFFICES ASSUME CJoint, [CNext]_CVars
               PROVE  CJoint'
    OBVIOUS
  <2>1. CASE \E self \in SafeAcceptors \times Messages : CSafeStep(self)
    <3> PICK self \in SafeAcceptors \times Messages : CSafeStep(self)
      BY <2>1
    <3>1. self[1] \in SafeAcceptors /\ self[2] \in Messages
            /\ self = <<self[1], self[2]>>
      OBVIOUS
    <3> QED
      BY <3>1, CJointSafeStep
  <2>2. CASE \E self \in ByzSenders : CByzStep(self)
    <3> PICK self \in ByzSenders : CByzStep(self)
      BY <2>2
    <3> QED
      BY CJointByzStep
  <2>3. CASE UNCHANGED CVars
    BY <2>3, CJointStutter
  <2> QED
    BY <2>1, <2>2, <2>3 DEF CNext
<1> QED
  BY <1>1, <1>2, PTL DEF CSpec
=============================================================================
