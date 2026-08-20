---------------------------- MODULE LiveSigRelElem ----------------------------
\* A live-SIGNED message on the network is live-relevant, boxed.  Clean-context
\* producer so consumers sitting under raw-temporal ambients (IAMEK, the
\* fairness assumptions, <>-hypotheses) can cite it instead of necessitating.
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

LEMMA LiveSigRelElem ==
  ASSUME NEW y, Sig(y) \in LiveAcceptors
  PROVE  Spec => [](y \in Msgs => y \in RelevantMsgs)
<1>1. Init => (y \in Msgs => y \in RelevantMsgs)
  BY DEF RelevantMsgs, LiveRelevant
<1>2. (y \in Msgs => y \in RelevantMsgs) /\ [Next]_vars
        => (y \in Msgs => y \in RelevantMsgs)'
  BY DEF RelevantMsgs, LiveRelevant
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
