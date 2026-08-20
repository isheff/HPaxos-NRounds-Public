------------------------- MODULE BoxKnownTranClosed -------------------------
\* KnownToLive is closed under TranExclusive at reachable states: whatever a
\* live acceptor knows, it knows the whole history of (KnownTranClosureInvT).
\* Per-pair box, the ever-known analogue of BoxTranClosed/BTCop; powers the
\* Tran-closedness of the ever-known allmessages set.
EXTENDS HPaxosPlusCal, AuxHoldsT
LOCAL INSTANCE TLAPS

LEMMA BoxKnownTranClosed ==
  ASSUME AcceptorsAssumptions, NEW mm \in Messages, NEW w, w \in TranExclusive(mm)
  PROVE  KTCop(mm, w)
<1> USE DEF KTCop
<1>state. AuxT /\ KnownToLive(mm) => KnownToLive(w)
  <2> SUFFICES ASSUME AuxT, KnownToLive(mm) PROVE KnownToLive(w)  OBVIOUS
  <2> PICK b \in LiveAcceptors : mm \in known_messages[b]  BY DEF KnownToLive
  <2>bs. b \in SafeAcceptors  BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
  <2>tc. TranClosure(known_messages[b]) = known_messages[b]
    BY <2>bs DEF AuxT, KnownTranClosureInvT
  <2>wt. w \in TranClosure(known_messages[b])  BY DEF TranClosure, TranExclusive
  <2>wk. w \in known_messages[b]  BY <2>wt, <2>tc
  <2> QED  BY <2>wk DEF KnownToLive
<1>aux. Spec => []AuxT  BY AuxHoldsT
<1> QED  BY <1>state, <1>aux, PTL DEF Spec
====================================================================
