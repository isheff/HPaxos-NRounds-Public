------------------------ MODULE CTranFairnessTransfer ------------------------
\* The termination theorems' extra hypothesis transfers too: if the concrete
\* spec is (unconditionally) weakly fair to every live acceptor's learn step
\* for every message in Tran(pp), so is the abstract spec.  Pointwise via the
\* ORIGINAL CWFTransferAt -- TranFairness's actions are the unrestricted
\* ones, so nothing about the weakening enters here; the only new content is
\* shrinking the pair domain to LiveAcceptors \X Tran(pp) (a subset of
\* LiveAcceptors \X Messages, by TranSubMessages).
\*
\* The \A over WF_ is routed through the opaque WFAbsTOp, as in
\* CLivenessTransfer: a quantifier over a TEMPORAL body cannot be
\* instantiated or introduced directly by any backend, but over an opaque
\* operator application it is ordinary first-order work.
EXTENDS HPaxosPlusCalConcrete, CWFTransferAt, TranSubMessages, TLAPS

WFAbsTOp(self) == WF_vars(safe_acceptor_receives_message(self))
WFConTOp(self) == WF_CVars(CSafeStep(self))

THEOREM CTranFairnessTransfer ==
  ASSUME ConcreteMessageInterface, AcceptorsAssumptions,
         TypeOKMessageInterface, NEW pp \in Messages
  PROVE  CSpec /\ CTranFairness(pp) => TranFairness(pp)
<1>tpsub. Tran(pp) \subseteq Messages
  BY TranSubMessages
<1>na. CSpec /\ CTranFairness(pp)
         => \A self \in LiveAcceptors \X Tran(pp) : WFAbsTOp(self)
  <2>1. \A self \in LiveAcceptors \X Tran(pp) :
          CSpec /\ CTranFairness(pp) => WFAbsTOp(self)
    <3> SUFFICES ASSUME NEW self \in LiveAcceptors \X Tran(pp)
                 PROVE  CSpec /\ CTranFairness(pp) => WFAbsTOp(self)
      OBVIOUS
    <3>m. self \in LiveAcceptors \X Messages
      BY <1>tpsub
    <3>1. CTranFairness(pp) => WFConTOp(self)
      BY DEF CTranFairness, WFConTOp
    <3>2. CSpec /\ WFConTOp(self) => WFAbsTOp(self)
      BY <3>m, CWFTransferAt DEF WFAbsTOp, WFConTOp
    <3> QED
      BY <3>1, <3>2
  <2> HIDE DEF WFAbsTOp
  <2> QED
    BY <2>1
<1> QED
  BY <1>na DEF TranFairness, WFAbsTOp
=============================================================================
