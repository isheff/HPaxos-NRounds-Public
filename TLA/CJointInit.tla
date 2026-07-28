--------------------------- MODULE CJointInit ---------------------------
\* The joint invariant holds initially.  Everything is empty, so the antichain
\* condition is CMMax({}) = {}.
EXTENDS HPaxosPlusCalConcrete, FiniteSetTheorems, TLAPS

LEMMA CJointInit == CInit => CJoint
<1> SUFFICES ASSUME CInit PROVE CJoint
  OBVIOUS
<1>i. Msgs = {} /\ known_messages = [t \in SafeAcceptors |-> {}]
      /\ recent_messages = [t \in SafeAcceptors |-> {}]
  BY DEF CInit
<1>1. CInv
  BY <1>i, FS_EmptySet DEF CInv
<1>2. KnownTranClosureInvT
  BY <1>i DEF KnownTranClosureInvT, TranClosure
<1>3. SelfSentBoundedInvT
  BY <1>i DEF SelfSentBoundedInvT
<1>4. CRecentIsMax
  BY <1>i DEF CRecentIsMax, CSelfSent, CMMax
<1> QED
  BY <1>1, <1>2, <1>3, <1>4 DEF CJoint
=============================================================================
