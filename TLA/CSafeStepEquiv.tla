--------------------------- MODULE CSafeStepEquiv ---------------------------
\* A concrete safe-acceptor step IS an abstract one together with the
\* recent_messages update.  Left-to-right is projection: the built candidate
\* is itself a forced-send witness, so every concrete transition is an
\* abstract one.  Right-to-left is lifting and needs canonicality of the sent
\* message (CSafeSentCanonical'): the abstract step may send ANY witness, but
\* a canonical witness is exactly the built candidate.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CSafeStepEquiv ==
  ASSUME NEW s \in SafeAcceptors, NEW x,
         known_messages \in [SafeAcceptors -> SUBSET Messages],
         CForcedSendAgreesAt(s, x)
  PROVE  /\ CSafeStep(<<s, x>>)
             => (/\ safe_acceptor_receives_message(<<s, x>>)
                 /\ recent_messages' = CRecentUpdate(s, x))
         /\ (/\ safe_acceptor_receives_message(<<s, x>>)
             /\ CSafeSentCanonical'
             /\ recent_messages' = CRecentUpdate(s, x))
             => CSafeStep(<<s, x>>)
<1> DEFINE Guard == /\ x \in Msgs
                    /\ TranExclusive(x) \subseteq known_messages[s]
                    /\ known_messages'
                         = [known_messages EXCEPT ![s] = known_messages[s] \cup {x}]
<1> DEFINE WS == {y \in (Messages \ Proposals) :
                    Sig(y) = s /\ TranExclusive(y) = CAT(s, x)}
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
  <2>fwd. CSafeStep(<<s, x>>)
            => (/\ safe_acceptor_receives_message(<<s, x>>)
                /\ recent_messages' = CRecentUpdate(s, x))
    <3> SUFFICES ASSUME CSafeStep(<<s, x>>)
                 PROVE  /\ safe_acceptor_receives_message(<<s, x>>)
                        /\ recent_messages' = CRecentUpdate(s, x)
      OBVIOUS
    <3>A. CASE CWellFormed(CCand(s, x))
      <4>net. Msgs' = Msgs \cup {CCand(s, x)}
        BY <3>A DEF CSafeStep, CCand, CRM
      <4>rec. recent_messages' = [recent_messages EXCEPT ![s] = {CCand(s, x)}]
        BY <3>A DEF CSafeStep, CCand, CRM
      <4>upd. recent_messages' = CRecentUpdate(s, x)
        BY <3>A, <4>rec DEF CRecentUpdate
      <4>wit. CCand(s, x) \in WS
        <5>1. /\ CCand(s, x) \in (Messages \ Proposals)
              /\ Sig(CCand(s, x)) = s
              /\ TranExclusive(CCand(s, x)) = CAT(s, x)
          BY <3>A DEF CForcedSendAgreesAt
        <5> QED BY <5>1
      <4>abs. safe_acceptor_receives_message(<<s, x>>)
        BY <1>3, <2>2, <4>net, <4>wit
        DEF safe_acceptor_receives_message
      <4> QED BY <4>abs, <4>upd
    <3>B. CASE ~CWellFormed(CCand(s, x))
      <4>net. Msgs' = Msgs
        BY <3>B DEF CSafeStep, CCand, CRM
      <4>rec. recent_messages' = [recent_messages EXCEPT ![s] = CRM(s, x)]
        BY <3>B DEF CSafeStep, CCand, CRM
      <4>upd. recent_messages' = CRecentUpdate(s, x)
        BY <3>B, <4>rec DEF CRecentUpdate
      <4>now. ~(\E y \in (Messages \ Proposals) :
                  Sig(y) = s /\ TranExclusive(y) = CAT(s, x))
        BY <3>B DEF CForcedSendAgreesAt
      <4>wempty. WS = {}
        BY <4>now
      <4>abs. safe_acceptor_receives_message(<<s, x>>)
        BY <1>3, <2>2, <4>net, <4>wempty
        DEF safe_acceptor_receives_message
      <4> QED BY <4>abs, <4>upd
    <3> QED BY <3>A, <3>B
  <2>bwd. (/\ safe_acceptor_receives_message(<<s, x>>)
           /\ CSafeSentCanonical'
           /\ recent_messages' = CRecentUpdate(s, x))
            => CSafeStep(<<s, x>>)
    <3> SUFFICES ASSUME safe_acceptor_receives_message(<<s, x>>),
                        CSafeSentCanonical',
                        recent_messages' = CRecentUpdate(s, x)
                 PROVE  CSafeStep(<<s, x>>)
      OBVIOUS
    <3>disj. \/ \E y \in WS : Msgs' = Msgs \cup {y}
             \/ (WS = {} /\ Msgs' = Msgs)
      BY <2>2 DEF safe_acceptor_receives_message
    <3>A. CASE \E y \in WS : Msgs' = Msgs \cup {y}
      <4>y. PICK y \in WS : Msgs' = Msgs \cup {y}  BY <3>A
      <4>yw. y \in (Messages \ Proposals) /\ Sig(y) = s
               /\ TranExclusive(y) = CAT(s, x)
        BY <4>y
      <4>wf. CWellFormed(CCand(s, x))
        BY <4>yw DEF CForcedSendAgreesAt
      <4>yin. y \in Msgs'
        BY <4>y
      <4>can. y.priors = Refs(y)
        BY <4>yin, <4>yw DEF CSafeSentCanonical
      <4>eq. y = CCand(s, x)
        BY <4>yw, <4>can DEF CForcedSendAgreesAt
      <4>net. Msgs' = Msgs \cup {CCand(s, x)}
        BY <4>y, <4>eq
      <4>rec. recent_messages' = [recent_messages EXCEPT ![s] = {CCand(s, x)}]
        BY <4>wf DEF CRecentUpdate
      <4> QED
        BY <1>3, <4>wf, <4>net, <4>rec DEF CSafeStep, CCand, CRM
    <3>B. CASE WS = {} /\ Msgs' = Msgs
      <4>nwf. ~CWellFormed(CCand(s, x))
        <5>1. CASE CWellFormed(CCand(s, x))
          <6>1. \E y \in (Messages \ Proposals) :
                  Sig(y) = s /\ TranExclusive(y) = CAT(s, x)
            BY <5>1 DEF CForcedSendAgreesAt
          <6>2. WS # {}  BY <6>1
          <6> QED BY <6>2, <3>B
        <5> QED BY <5>1
      <4>rec. recent_messages' = [recent_messages EXCEPT ![s] = CRM(s, x)]
        BY <4>nwf DEF CRecentUpdate
      <4> QED
        BY <1>3, <4>nwf, <3>B, <4>rec DEF CSafeStep, CCand, CRM
    <3> QED BY <3>disj, <3>A, <3>B
  <2> QED BY <2>fwd, <2>bwd
<1>4. CASE ~Guard
  BY <1>1, <1>2, <1>4
<1> QED
  BY <1>3, <1>4
=============================================================================
