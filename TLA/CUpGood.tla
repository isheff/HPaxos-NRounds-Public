--------------------------- MODULE CUpGood ---------------------------
\* The knowledge set ENLARGED by the message just received is still finite,
\* Tran-closed, and made of already-sent messages.  Adding x is safe because
\* the receive guard puts its whole strict history inside known_messages[s].
EXTENDS HPaxosPlusCalConcrete, CUGood, FiniteSetTheorems, TLAPS

LEMMA CUpGood ==
  ASSUME ConcreteMessageInterface,
         NEW s \in SafeAcceptors, NEW x \in Messages,
         x \in Msgs, TranExclusive(x) \subseteq known_messages[s],
         CInv, KnownTranClosureInvT, SelfSentBoundedInvT
  PROVE  LET Up == (known_messages[s] \cup {x}) \cup CSelfSent(s)
         IN  /\ Up \subseteq Messages
             /\ IsFiniteSet(Up)
             /\ \A z \in Up : Tran(z) \subseteq Up
             /\ Up \subseteq Msgs
<1> DEFINE U  == UOf(s)
<1> DEFINE Up == (known_messages[s] \cup {x}) \cup CSelfSent(s)
<1>good. /\ U \subseteq Messages
         /\ IsFiniteSet(U)
         /\ \A z \in U : Tran(z) \subseteq U
  BY CUGood
<1>eq. Up = U \cup {x}
  BY DEF UOf
<1>msgs. U \subseteq Msgs
  BY DEF CInv, UOf, CSelfSent
<1>1. Up \subseteq Messages
  BY <1>eq, <1>good
<1>2. IsFiniteSet(Up)
  BY <1>eq, <1>good, FS_AddElement
<1>3. Up \subseteq Msgs
  BY <1>eq, <1>msgs
<1>4. \A z \in Up : Tran(z) \subseteq Up
  <2> SUFFICES ASSUME NEW z \in Up
               PROVE  Tran(z) \subseteq Up
    OBVIOUS
  <2>1. CASE z \in U
    BY <2>1, <1>good, <1>eq
  <2>2. CASE z = x
    <3>1. Tran(x) = {x} \cup TranExclusive(x)
      BY DEF TranExclusive, Tran
    <3>2. TranExclusive(x) \subseteq U
      BY DEF UOf
    <3> QED
      BY <2>2, <3>1, <3>2, <1>eq
  <2> QED
    BY <2>1, <2>2, <1>eq
<1> QED
  BY <1>1, <1>2, <1>3, <1>4
=============================================================================
