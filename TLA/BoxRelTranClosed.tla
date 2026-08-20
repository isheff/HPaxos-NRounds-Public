-------------------------- MODULE BoxRelTranClosed --------------------------
\* The load-bearing closure fact of the weakened liveness chain: at reachable
\* states, RelevantMsgs is closed under TranExclusive.  A live-signed
\* message's exclusive history is bounded by its signer's knowledge plus its
\* signer's own sent messages (SelfSentBoundedInvT); a known message's
\* history is known (KnownTranClosureInvT).  Either way every history element
\* is again live-relevant, and in Msgs by Inv.
EXTENDS HPaxosPlusCal, AuxHoldsT
LOCAL INSTANCE TLAPS

LEMMA BoxRelTranClosed ==
  ASSUME AcceptorsAssumptions, NEW xx \in Messages, NEW w, w \in TranExclusive(xx)
  PROVE  BTCRop(xx, w)
<1> USE DEF BTCRop
<1>state. AuxT /\ {xx} \subseteq RelevantMsgs => w \in RelevantMsgs
  <2> SUFFICES ASSUME AuxT, xx \in RelevantMsgs PROVE w \in RelevantMsgs  OBVIOUS
  <2>inv. Inv  BY DEF AuxT
  <2>xm. xx \in Msgs /\ LiveRelevant(xx)  BY DEF RelevantMsgs
  <2>wm. w \in Msgs  BY <2>inv, <2>xm DEF Inv
  <2>c1. CASE Sig(xx) \in LiveAcceptors
    <3>s. Sig(xx) \in SafeAcceptors
      BY <2>c1 DEF AcceptorsAssumptions, LiveAcceptorsAssumption
    <3>ssb. TranExclusive(xx) \subseteq
              known_messages[Sig(xx)] \cup {m \in Msgs : Sig(m) = Sig(xx)}
      BY <3>s, <2>xm DEF AuxT, SelfSentBoundedInvT
    <3>ck. CASE w \in known_messages[Sig(xx)]
      BY <3>ck, <2>wm, <2>c1 DEF RelevantMsgs, LiveRelevant
    <3>cs. CASE w \in {m \in Msgs : Sig(m) = Sig(xx)}
      BY <3>cs, <2>wm, <2>c1 DEF RelevantMsgs, LiveRelevant
    <3> QED  BY <3>ssb, <3>ck, <3>cs
  <2>c2. CASE \E b \in LiveAcceptors : xx \in known_messages[b]
    <3> PICK b \in LiveAcceptors : xx \in known_messages[b]  BY <2>c2
    <3>bs. b \in SafeAcceptors
      BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
    <3>tc. TranClosure(known_messages[b]) = known_messages[b]
      BY <3>bs DEF AuxT, KnownTranClosureInvT
    <3>wt. w \in TranClosure(known_messages[b])
      BY DEF TranClosure, TranExclusive
    <3>wk. w \in known_messages[b]  BY <3>wt, <3>tc
    <3> QED  BY <3>wk, <2>wm DEF RelevantMsgs, LiveRelevant
  <2> QED  BY <2>xm, <2>c1, <2>c2 DEF LiveRelevant
<1>aux. Spec => []AuxT  BY AuxHoldsT
<1> QED  BY <1>state, <1>aux, PTL DEF Spec
====================================================================
