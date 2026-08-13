--------------------------- MODULE CLivenessTransfer ---------------------------
\* THE THEOREM.  Everything HPaxosPlusCal's liveness results assume,
\* HPaxosPlusCalConcrete supplies:
\*
\*     CSpec /\ CNetworkAssumption  =>  Spec /\ NetworkAssumption
\*
\* so any abstract result of the form (Spec /\ NetworkAssumption => L) --
\* EventuallyKnownInvariant, the leads-to chain, termination -- applies to the
\* concrete spec verbatim, by modus ponens, with no re-proof.
\*
\* The left conjunct is refinement (CRefinesAbstract) and was already available.
\* The right conjunct is the new content and is NOT a consequence of refinement:
\* refinement says the concrete spec does nothing NEW, whereas a fairness
\* hypothesis is a promise that it does not do LESS.  Pinning recent_messages
\* could a priori have disabled abstract steps, which would make
\* CNetworkAssumption's weak fairness satisfiable vacuously -- true of a
\* concrete behaviour that starves the very step NetworkAssumption promises to
\* take -- and every abstract eventuality would evaporate.  CWFTransferAt rules
\* that out process by process, from CEnabledTransfer's ENABLED transfer plus
\* CSafeStepAngle's converse step projection.
\*
\* Only safe-acceptor processes appear: both fairness assumptions quantify over
\* LiveAcceptors \X Messages, and Byzantine senders are never assumed fair.
\*
\* The \A over WF_ is routed through the opaque WFAbsOp: a quantifier over a
\* TEMPORAL body cannot be instantiated or introduced directly by any backend,
\* but over an opaque operator application it is ordinary first-order work.
EXTENDS HPaxosPlusCalConcrete, CWFTransferAt, CRefinesAbstract, TLAPS

WFAbsOp(self) == WF_vars(safe_acceptor_receives_message(self))
WFConOp(self) == WF_CVars(CSafeStep(self))

THEOREM CLivenessTransfer ==
  ASSUME ConcreteMessageInterface, AcceptorsAssumptions
  PROVE  CSpec /\ CNetworkAssumption => Spec /\ NetworkAssumption
<1>saa. SafeAcceptorsAssumption
  BY DEF AcceptorsAssumptions
<1>ref. CSpec => Spec
  BY <1>saa, CRefinesAbstract
<1>na. CSpec /\ CNetworkAssumption
         => \A self \in LiveAcceptors \X Messages : WFAbsOp(self)
  <2>1. \A self \in LiveAcceptors \X Messages :
          CSpec /\ CNetworkAssumption => WFAbsOp(self)
    <3> SUFFICES ASSUME NEW self \in LiveAcceptors \X Messages
                 PROVE  CSpec /\ CNetworkAssumption => WFAbsOp(self)
      OBVIOUS
    <3>1. CNetworkAssumption => WFConOp(self)
      BY DEF CNetworkAssumption, WFConOp
    <3>2. CSpec /\ WFConOp(self) => WFAbsOp(self)
      BY CWFTransferAt DEF WFAbsOp, WFConOp
    <3> QED
      BY <3>1, <3>2
  <2> HIDE DEF WFAbsOp
  <2> QED
    BY <2>1
<1> QED
  BY <1>ref, <1>na DEF NetworkAssumption, WFAbsOp
=============================================================================
