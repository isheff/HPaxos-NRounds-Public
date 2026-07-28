--------------------------- MODULE CJointStutter ---------------------------
\* The joint invariant is preserved by stuttering: it mentions only Msgs,
\* known_messages and recent_messages, all of which CVars holds fixed.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CJointStutter == CJoint /\ UNCHANGED CVars => CJoint'
BY DEF CJoint, CInv, KnownTranClosureInvT, SelfSentBoundedInvT, CRecentIsMax,
       CSelfSent, CVars
=============================================================================
