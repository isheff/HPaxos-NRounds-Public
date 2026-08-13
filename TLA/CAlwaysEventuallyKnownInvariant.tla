------------------- MODULE CAlwaysEventuallyKnownInvariant -------------------
\* Worked example of CLivenessTransfer: an abstract liveness result, restated
\* for HPaxosPlusCalConcrete and discharged by modus ponens alone.
\*
\* Nothing about the concrete spec is re-proven here.  CLivenessTransfer turns
\* the concrete hypotheses into the abstract ones, and
\* AlwaysEventuallyKnownInvariant is then applied unchanged.  Every other
\* abstract result with hypotheses (Spec /\ NetworkAssumption /\ constants)
\* transfers by exactly this three-line proof -- which is the point of
\* CLivenessTransfer, and the reason it is worth stating in that form.
EXTENDS HPaxosPlusCalConcrete, CLivenessTransfer,
        AlwaysEventuallyKnownInvariant, TLAPS

THEOREM CAlwaysEventuallyKnownInvariant ==
  (/\ CSpec
   /\ ConcreteMessageInterface
   /\ MessageInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ AcceptorsAssumptions
   /\ CNetworkAssumption
  ) => []EventuallyKnownInvariant
<1> SUFFICES ASSUME CSpec, ConcreteMessageInterface,
                    MessageInterfaceAssumptions, LearnerGraphAssumptions,
                    AcceptorsAssumptions, CNetworkAssumption
             PROVE  []EventuallyKnownInvariant
  OBVIOUS
<1>1. Spec /\ NetworkAssumption
  BY CLivenessTransfer
<1> QED
  BY <1>1, AlwaysEventuallyKnownInvariant
=============================================================================
