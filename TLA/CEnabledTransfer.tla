--------------------------- MODULE CEnabledTransfer ---------------------------
\* THE THEOREM.  At every reachable state of HPaxosPlusCalConcrete, every
\* action HPaxosPlusCal could take, HPaxosPlusCalConcrete can take too.
\*
\* HPaxosPlusCalConcreteSpecEquivalence gives CSpec <=> (Spec /\ []CRecentOK /\
\* []CSafeSentCanonical).  Read left to right that is refinement, and SAFETY
\* transfers immediately: an invariant of HPaxosPlusCal is an invariant of
\* HPaxosPlusCalConcrete.  LIVENESS does not follow the same way.  A safety
\* proof only needs that the concrete spec does nothing new; a liveness proof
\* needs that it does not do LESS -- that the concrete spec has not, by pinning
\* recent_messages, quietly disabled steps the abstract one could take.  If it
\* had, CNetworkAssumption's weak fairness would be satisfiable vacuously where
\* NetworkAssumption's is not, and every abstract eventuality would be lost.
\*
\* This theorem closes that gap, pointwise on processes and in the angle-
\* bracket form weak fairness actually uses.  It is the missing premise for
\* CNetworkAssumption => NetworkAssumption, and hence for reusing every
\* liveness result proven about HPaxosPlusCal.
\*
\* Neither direction is free.  For the safe-acceptor step the abstract action
\* may send ANY forced-send witness while the concrete one builds a specific
\* record, so the two could a priori disagree about when a send is possible;
\* they do not, because a witness exists exactly when the built record is well
\* formed, and among the witnesses there is always the canonical one -- priors
\* exactly Refs -- which IS the built record (CForcedSendAgreesAt).  See
\* CSafeStepEnabled.  For a Byzantine sender nothing is needed at all: the
\* action is HPaxosPlusCal's verbatim (CByzStepEnabled).
\*
\* The invariant hypothesis enters only through CJoint, so `reachable state'
\* here means reachable under CSpec, via CJointHolds.
EXTENDS HPaxosPlusCalConcrete, CSafeStepEnabled, CByzStepEnabled,
        CJointHolds, TLAPS

\* Operator-wrapped so the conclusion can be instantiated at a concrete
\* process without unfolding anything ENABLED-shaped at the call site.
CEnabledAt(self) ==
  ENABLED <<safe_acceptor_receives_message(self)>>_vars
    => ENABLED <<CSafeStep(self)>>_CVars

CByzEnabledAt(self) ==
  ENABLED <<byz(self)>>_vars => ENABLED <<CByzStep(self)>>_CVars

THEOREM CEnabledTransfer ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption
  PROVE  CSpec => [](/\ \A self \in SafeAcceptors \X Messages : CEnabledAt(self)
                     /\ \A self \in ByzSenders : CByzEnabledAt(self))
<1>1. CJoint => (/\ \A self \in SafeAcceptors \X Messages : CEnabledAt(self)
                 /\ \A self \in ByzSenders : CByzEnabledAt(self))
  <2> SUFFICES ASSUME CJoint
               PROVE  /\ \A self \in SafeAcceptors \X Messages : CEnabledAt(self)
                      /\ \A self \in ByzSenders : CByzEnabledAt(self)
    OBVIOUS
  <2>1. \A self \in SafeAcceptors \X Messages : CEnabledAt(self)
    <3> SUFFICES ASSUME NEW self \in SafeAcceptors \X Messages,
                        ENABLED <<safe_acceptor_receives_message(self)>>_vars
                 PROVE  ENABLED <<CSafeStep(self)>>_CVars
      BY DEF CEnabledAt
    <3> QED
      BY CSafeStepEnabled
  <2>2. \A self \in ByzSenders : CByzEnabledAt(self)
    <3> SUFFICES ASSUME NEW self \in ByzSenders,
                        ENABLED <<byz(self)>>_vars
                 PROVE  ENABLED <<CByzStep(self)>>_CVars
      BY DEF CByzEnabledAt
    <3> QED
      BY CByzStepEnabled
  <2> QED
    BY <2>1, <2>2
<1>2. CSpec => []CJoint
  BY CJointHolds
<1> QED
  BY <1>1, <1>2, PTL
=============================================================================
