--------------------------- MODULE CUGood ---------------------------
\* "Everything s knows or has sent" is a finite, Tran-closed set of messages.
\* Tran-closedness is where HPaxosPlusCal's own two auxiliary invariants get
\* used: KnownTranClosureInvT for what s was told, SelfSentBoundedInvT for what
\* s sent.
EXTENDS HPaxosPlusCalConcrete, FiniteSetTheorems, TLAPS

LEMMA CUGood ==
  ASSUME ConcreteMessageInterface, NEW s \in SafeAcceptors,
         CInv, KnownTranClosureInvT, SelfSentBoundedInvT
  PROVE  /\ UOf(s) \subseteq Messages
         /\ IsFiniteSet(UOf(s))
         /\ \A z \in UOf(s) : Tran(z) \subseteq UOf(s)
<1>sub. UOf(s) \subseteq Msgs
  BY DEF CInv, UOf, CSelfSent
<1>1. UOf(s) \subseteq Messages
  BY <1>sub DEF CInv
<1>2. IsFiniteSet(UOf(s))
  BY <1>sub, FS_Subset DEF CInv
<1>3. \A z \in UOf(s) : Tran(z) \subseteq UOf(s)
  <2> SUFFICES ASSUME NEW z \in UOf(s)
               PROVE  Tran(z) \subseteq UOf(s)
    OBVIOUS
  <2>1. CASE z \in known_messages[s]
    <3>1. Tran(z) \subseteq TranClosure(known_messages[s])
      BY <2>1 DEF TranClosure
    <3> QED
      BY <3>1 DEF KnownTranClosureInvT, UOf
  <2>2. CASE z \in CSelfSent(s)
    <3>1. z \in Msgs /\ Sig(z) = s
      BY <2>2 DEF CSelfSent
    <3>2. TranExclusive(z) \subseteq known_messages[s] \cup {m \in Msgs : Sig(m) = s}
      BY <3>1 DEF SelfSentBoundedInvT
    <3>3. Tran(z) = {z} \cup TranExclusive(z)
      BY DEF TranExclusive, Tran
    <3> QED
      BY <2>2, <3>2, <3>3 DEF UOf, CSelfSent
  <2> QED
    BY <2>1, <2>2 DEF UOf
<1> QED
  BY <1>1, <1>2, <1>3
=============================================================================
