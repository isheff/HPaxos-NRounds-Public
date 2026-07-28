--------------------------- MODULE CBuiltInCMC ---------------------------
\* A record built over finitely many already-sent priors is in CMC.
\* CMCFromShape does the work; all that is needed is that the priors are a
\* finite subset of CMC.
EXTENDS HPaxosPlusCalConcrete, CMCFromShape, CMessagesSubMC, TLAPS

LEMMA CBuiltInCMC ==
  ASSUME NEW sdr \in CSenders, NEW pl \in CPayload,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr)
  PROVE  [sender |-> sdr, payload |-> pl, priors |-> pr] \in CMC
<1> DEFINE cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
<1>1. pr \subseteq CMC
  BY CMessagesSubMC
<1>2. cand \in [sender : CSenders, payload : CPayload, priors : SUBSET CMC]
  BY <1>1
<1>3. cand.priors = pr
  OBVIOUS
<1> QED
  BY <1>2, <1>3, CMCFromShape
=============================================================================
