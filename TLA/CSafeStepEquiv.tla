--------------------------- MODULE CSafeStepEquiv ---------------------------
\* A concrete safe-acceptor step IS an abstract one together with the
\* (uniquely determined) update to recent_messages.  Left-to-right is
\* projection: every concrete transition is an abstract one.  Right-to-left is
\* lifting: every abstract transition is realised, with the one
\* recent_messages' that CSafeStep computes.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CSafeStepEquiv ==
  ASSUME NEW s \in SafeAcceptors, NEW x,
         known_messages \in [SafeAcceptors -> SUBSET Messages],
         CForcedSendAgreesAt(s, x)
  PROVE  CSafeStep(<<s, x>>)
           <=> (/\ safe_acceptor_receives_message(<<s, x>>)
                /\ recent_messages' = CRecentUpdate(s, x))
<1> DEFINE Guard == /\ x \in Msgs
                    /\ TranExclusive(x) \subseteq known_messages[s]
                    /\ known_messages'
                         = [known_messages EXCEPT ![s] = known_messages[s] \cup {x}]
\* Both actions open with Guard, verbatim.
<1>1. CSafeStep(<<s, x>>) => Guard
  BY DEF CSafeStep
<1>2. safe_acceptor_receives_message(<<s, x>>) => Guard
  BY DEF safe_acceptor_receives_message
<1>3. CASE Guard
  \* Under Guard the abstract action's T is CAT(s, x).  Kept as its own step:
  \* SMT treats known_messages'[s] and the EXCEPT term as unrelated atoms, so
  \* the index equality has to be established before it can be used.
  <2>1. known_messages'[s] = known_messages[s] \cup {x}
    BY <1>3
  <2>2. (known_messages'[s] \cup {x}) \cup {m \in Msgs : Sig(m) = s} = CAT(s, x)
    BY <2>1 DEF CAT, CSelfSent
  <2>3. CASE CWellFormed(CCand(s, x))
    <3>1. \E y \in (Messages \ Proposals) : Sig(y) = s /\ TranExclusive(y) = CAT(s, x)
      BY <2>3 DEF CForcedSendAgreesAt
    <3>2. CCand(s, x) = (CHOOSE y \in (Messages \ Proposals) :
                            Sig(y) = s /\ TranExclusive(y) = CAT(s, x))
      BY <2>3 DEF CForcedSendAgreesAt
    <3> QED
      BY <1>3, <2>2, <2>3, <3>1, <3>2
      DEF CSafeStep, safe_acceptor_receives_message,
          CCand, CRM, CRecentUpdate
  <2>4. CASE ~CWellFormed(CCand(s, x))
    <3>1. ~(\E y \in (Messages \ Proposals) : Sig(y) = s /\ TranExclusive(y) = CAT(s, x))
      BY <2>4 DEF CForcedSendAgreesAt
    <3> QED
      BY <1>3, <2>2, <2>4, <3>1
      DEF CSafeStep, safe_acceptor_receives_message,
          CCand, CRM, CRecentUpdate
  <2> QED
    BY <2>3, <2>4
<1>4. CASE ~Guard
  BY <1>1, <1>2, <1>4
<1> QED
  BY <1>3, <1>4
=============================================================================
