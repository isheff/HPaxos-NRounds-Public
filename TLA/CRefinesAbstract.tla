--------------------------- MODULE CRefinesAbstract ---------------------------
\* CSpec => Spec.  Looking only at Msgs and known_messages -- the variables
\* HPaxosPlusCal declares -- every behaviour of the concrete spec is a
\* behaviour of the abstract one.
EXTENDS HPaxosPlusCalConcrete, CInitEquiv, CNextProjects, CAgreesFromJoint,
        CJointHolds, TLAPS

LEMMA CRefinesAbstract ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption
  PROVE  CSpec => Spec
<1>1. CInit => Init
  BY CInitEquiv
<1>2. CJoint /\ [CNext]_CVars => [Next]_vars
  <2> SUFFICES ASSUME CJoint, [CNext]_CVars
               PROVE  [Next]_vars
    OBVIOUS
  <2>1. CASE CNext
    <3>1. known_messages \in [SafeAcceptors -> SUBSET Messages]
      BY DEF CJoint, CInv
    <3>2. \A s \in SafeAcceptors : \A x \in Messages :
            (x \in Msgs /\ TranExclusive(x) \subseteq known_messages[s])
              => CForcedSendAgreesAt(s, x)
      BY CAgreesFromJoint
    <3>3. Next
      BY <2>1, <3>1, <3>2, CNextProjects
    <3> QED
      BY <3>3
  <2>2. CASE UNCHANGED CVars
    BY <2>2 DEF CVars, vars
  <2> QED
    BY <2>1, <2>2
<1>3. CSpec => []CJoint
  BY CJointHolds
<1>4. CSpec => [][CNext]_CVars
  BY PTL DEF CSpec
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, PTL DEF CSpec, Spec
=============================================================================
