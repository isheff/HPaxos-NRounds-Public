--------------------------- MODULE CRMIsMax ---------------------------
\* THE HEART of the invariant: the value assigned to recent_messages[s] before
\* the send is considered is exactly the maximal antichain of the ENLARGED
\* knowledge set.  The two branches of CRM are the two cases here.
\*
\* Case 1 is why the update SKIPS a message already in known \cup CSelfSent:
\* the knowledge set does not move, so neither may the antichain over it.
EXTENDS HPaxosPlusCalConcrete, CUGood, CMMaxAddNew, CNotInOwnPriors, TLAPS

LEMMA CRMIsMax ==
  ASSUME ConcreteMessageInterface,
         NEW s \in SafeAcceptors, NEW x \in Messages,
         x \in Msgs,
         TranExclusive(x) \subseteq known_messages[s],
         CInv, KnownTranClosureInvT, SelfSentBoundedInvT, CRecentIsMax
  PROVE  CRM(s, x) = CMMax((known_messages[s] \cup {x}) \cup CSelfSent(s))
<1> DEFINE U  == UOf(s)
<1> DEFINE Up == (known_messages[s] \cup {x}) \cup CSelfSent(s)
<1>good. /\ U \subseteq Messages
         /\ IsFiniteSet(U)
         /\ \A z \in U : Tran(z) \subseteq U
  BY CUGood
<1>max. recent_messages[s] = CMMax(U)
  BY DEF CRecentIsMax, UOf
\* Case 1: x is already accounted for, so the knowledge set does not move.
<1>1. CASE x \in known_messages[s] \/ Sig(x) = s
  <2>1. Up = U
    <3>1. CASE x \in known_messages[s]
      BY <3>1 DEF UOf
    <3>2. CASE Sig(x) = s
      <4>1. x \in CSelfSent(s)
        BY <3>2 DEF CSelfSent
      <4> QED
        BY <4>1 DEF UOf
    <3> QED
      BY <1>1, <3>1, <3>2
  <2>2. CRM(s, x) = recent_messages[s]
    BY <1>1 DEF CRM
  <2> QED
    BY <1>max, <2>1, <2>2
\* Case 2: x is genuinely new -- add it and drop the priors it dominates.
<1>2. CASE ~(x \in known_messages[s] \/ Sig(x) = s)
  <2>1. x \notin U
    <3>1. x \notin known_messages[s]
      BY <1>2
    <3>2. x \notin CSelfSent(s)
      BY <1>2 DEF CSelfSent
    <3> QED
      BY <3>1, <3>2 DEF UOf
  <2>2. TranExclusive(x) \subseteq U
    BY DEF UOf
  <2>3. CMMax(U \cup {x}) = (CMMax(U) \ x.priors) \cup {x}
    BY <1>good, <2>1, <2>2, CMMaxAddNew
  <2>4. Up = U \cup {x}
    BY DEF UOf
  <2>5. x \notin x.priors
    BY CNotInOwnPriors
  <2>6. CRM(s, x) = (recent_messages[s] \cup {x}) \ x.priors
    BY <1>2 DEF CRM
  <2>7. (recent_messages[s] \cup {x}) \ x.priors
          = (recent_messages[s] \ x.priors) \cup {x}
    BY <2>5
  <2> QED
    BY <1>max, <2>3, <2>4, <2>6, <2>7
<1> QED
  BY <1>1, <1>2
=============================================================================
