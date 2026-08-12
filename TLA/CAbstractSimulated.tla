--------------------------- MODULE CAbstractSimulated ---------------------------
\* Spec plus the pinned bookkeeping gives the concrete spec.
\*
\* AuxHoldsT is what makes this direction cheap: the abstract development
\* already proves Spec => []AuxT, and AuxT contains exactly the three
\* invariants the forced-send agreement needs.  Going THIS way they can be
\* inherited -- the circularity that forced CJointHolds to prove them from
\* scratch ran through CNext => Next, which is not what is established here.
EXTENDS HPaxosPlusCalConcrete, CNextFromNext, CJointFromAux, AuxHoldsT, TLAPS

LEMMA CAbstractSimulated ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption
  PROVE  Spec /\ []CRecentOK /\ []CSafeSentCanonical => CSpec
<1>init. Init /\ CRecentOK => CInit
  <2> SUFFICES ASSUME Init, CRecentOK PROVE CInit
    OBVIOUS
  <2>1. Msgs = {} /\ known_messages = [s \in SafeAcceptors |-> {}]
    BY DEF Init
  <2>2. \A t \in SafeAcceptors : recent_messages[t] = {}
    <3> SUFFICES ASSUME NEW t \in SafeAcceptors PROVE recent_messages[t] = {}
      OBVIOUS
    <3>1. known_messages[t] \cup CSelfSent(t) = {}
      BY <2>1 DEF CSelfSent
    <3> QED
      BY <3>1 DEF CRecentOK, CRecentIsMax, CMMax
  <2>3. recent_messages \in [SafeAcceptors -> SUBSET Messages]
    BY DEF CRecentOK
  <2> QED
    BY <2>1, <2>2, <2>3 DEF CInit
<1>aux. Spec => []AuxT
  BY AuxHoldsT
<1>joint. AuxT /\ CRecentOK => CJoint
  BY CJointFromAux
<1>step. CJoint /\ CRecentOK' /\ CSafeSentCanonical' /\ [Next]_vars
           => [CNext]_CVars
  BY CNextFromNext
<1> QED
  BY <1>init, <1>aux, <1>joint, <1>step, PTL DEF Spec, CSpec
=============================================================================
