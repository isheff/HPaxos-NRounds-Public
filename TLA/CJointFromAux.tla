--------------------------- MODULE CJointFromAux ---------------------------
\* The abstract development's AuxT plus the pinned bookkeeping gives the joint
\* invariant.  CInv is Inv plus two facts about recent_messages: its typing,
\* which CRecentOK supplies directly, and recent_messages[s] \subseteq Msgs,
\* which holds because the antichain sits inside the set it is taken over.
EXTENDS HPaxosPlusCalConcrete, AuxHoldsT, TLAPS

LEMMA CJointFromAux ==
  ASSUME AuxT, CRecentOK
  PROVE  CJoint
<1>1. Inv
  BY DEF AuxT
<1>2. \A t \in SafeAcceptors : recent_messages[t] \subseteq Msgs
  <2> SUFFICES ASSUME NEW t \in SafeAcceptors
               PROVE  recent_messages[t] \subseteq Msgs
    OBVIOUS
  <2>1. recent_messages[t] = CMMax(known_messages[t] \cup CSelfSent(t))
    BY DEF CRecentOK, CRecentIsMax
  <2>2. known_messages[t] \cup CSelfSent(t) \subseteq Msgs
    BY <1>1 DEF Inv, CSelfSent
  <2> QED
    BY <2>1, <2>2 DEF CMMax
<1>3. CInv
  BY <1>1, <1>2 DEF Inv, CInv, CRecentOK
<1> QED
  BY <1>3 DEF AuxT, CJoint, CRecentOK
=============================================================================
