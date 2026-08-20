--------------------------- MODULE KnownToLiveElem ---------------------------
\* Membership in a LIVE acceptor's knowledge witnesses KnownToLive, boxed.
\* Clean-context producer for consumers under raw-temporal ambients.
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

LEMMA KnownToLiveElem ==
  ASSUME NEW a \in LiveAcceptors, NEW xx
  PROVE  KTLElemOp(a, xx)
<1> USE DEF KTLElemOp
<1>1. Init => (xx \in known_messages[a] => KnownToLive(xx))  BY DEF KnownToLive
<1>2. (xx \in known_messages[a] => KnownToLive(xx)) /\ [Next]_vars
        => (xx \in known_messages[a] => KnownToLive(xx))'  BY DEF KnownToLive
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
