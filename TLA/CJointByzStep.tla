--------------------------- MODULE CJointByzStep ---------------------------
\* Byzantine steps preserve the joint invariant trivially: they touch neither
\* known_messages nor recent_messages, and the message they add is signed by a
\* non-safe sender, so no safe acceptor's CSelfSent -- and hence no antichain --
\* moves either.
EXTENDS HPaxosPlusCalConcrete, FiniteSetTheorems, TLAPS

LEMMA CJointByzStep ==
  ASSUME ConcreteMessageInterface,
         CJoint, NEW self \in ByzSenders, CByzStep(self)
  PROVE  CJoint'
<1>inv. CInv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ CRecentIsMax
  BY DEF CJoint
<1>ns. self \notin SafeAcceptors
  BY DEF ByzSenders
<1> PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
      Msgs' = Msgs \cup {y}
  BY DEF CByzStep
<1>y. y \in Messages /\ Sig(y) = self /\ TranExclusive(y) \subseteq Msgs
  OBVIOUS
<1>unch. known_messages' = known_messages /\ recent_messages' = recent_messages
  BY DEF CByzStep
<1>self. \A t \in SafeAcceptors : {m \in Msgs' : Sig(m) = t} = CSelfSent(t)
  BY <1>ns, <1>y DEF CSelfSent
<1>1. CInv'
  <2>1. Msgs' \in SUBSET Messages
    BY <1>y, <1>inv DEF CInv
  <2>2. IsFiniteSet(Msgs')
    BY <1>inv, FS_AddElement DEF CInv
  <2>3. \A z \in Msgs' : TranExclusive(z) \subseteq Msgs'
    BY <1>y, <1>inv DEF CInv
  <2> QED
    BY <2>1, <2>2, <2>3, <1>unch, <1>inv DEF CInv
<1>2. SelfSentBoundedInvT'
  <3> SUFFICES ASSUME NEW t \in SafeAcceptors, NEW z \in Msgs', Sig(z) = t
               PROVE  TranExclusive(z)
                        \subseteq known_messages'[t] \cup {m \in Msgs' : Sig(m) = t}
    BY DEF SelfSentBoundedInvT
  <3>1. z \in Msgs
    BY <1>ns, <1>y
  <3>2. TranExclusive(z) \subseteq known_messages[t] \cup {m \in Msgs : Sig(m) = t}
    BY <3>1, <1>inv DEF SelfSentBoundedInvT
  <3> QED
    BY <3>2, <1>unch
<1>3. CRecentIsMax'
  BY <1>unch, <1>self, <1>inv DEF CRecentIsMax, CSelfSent
<1> QED
  BY <1>1, <1>2, <1>3, <1>unch, <1>inv DEF CJoint, KnownTranClosureInvT
=============================================================================
