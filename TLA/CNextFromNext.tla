--------------------------- MODULE CNextFromNext ---------------------------
\* An abstract step, together with the pinned bookkeeping, IS a concrete step.
\* This is the lifting direction: nothing HPaxosPlusCal can do is lost.
\*
\* The work is showing that the pinned recent_messages' is precisely the value
\* CSafeStep computes -- on a send the antichain collapses to the message just
\* sent (CMMaxAddTop), otherwise it is what CRM computed (CRMIsMax).
EXTENDS HPaxosPlusCalConcrete, CSafeGuardsIdentical, CAgreesFromJoint,
        CUpGood, CRMIsMax, CCandFacts, CMMaxAddTop, CSafeStepEquiv,
        CByzEquiv, TLAPS

LEMMA CNextFromNext ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption,
         CJoint, CRecentOK', CSafeSentCanonical', [Next]_vars
  PROVE  [CNext]_CVars
<1>inv. CInv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ CRecentIsMax
  BY DEF CJoint
<1>rok. recent_messages' \in [SafeAcceptors -> SUBSET Messages]
        /\ (\A t \in SafeAcceptors :
              recent_messages'[t] = CMMax(known_messages'[t] \cup {m \in Msgs' : Sig(m) = t}))
  BY DEF CRecentOK, CRecentIsMax, CSelfSent
<1>rtyp. recent_messages \in [SafeAcceptors -> SUBSET Messages]
  BY <1>inv DEF CInv
<1>1. CASE \E self \in SafeAcceptors \times Messages :
             safe_acceptor_receives_message(self)
  <2> PICK self \in SafeAcceptors \times Messages :
             safe_acceptor_receives_message(self)
    BY <1>1
  <2>1. self[1] \in SafeAcceptors /\ self[2] \in Messages
          /\ self = <<self[1], self[2]>>
    OBVIOUS
  <2> DEFINE s == self[1]
  <2> DEFINE x == self[2]
  <2> DEFINE Up   == (known_messages[s] \cup {x}) \cup CSelfSent(s)
  <2> DEFINE rm   == CRM(s, x)
  <2> DEFINE cand == CCand(s, x)
  <2>g. x \in Msgs /\ TranExclusive(x) \subseteq known_messages[s]
    BY <2>1, CSafeGuardsIdentical
  <2>agree. CForcedSendAgreesAt(s, x)
    BY <2>1, <2>g, CAgreesFromJoint DEF CJoint
  \* The abstract action already fixes known_messages' and -- via the
  \* agreement -- Msgs'; both are exactly what CSafeStep asks for.
  <2>km. known_messages'
           = [known_messages EXCEPT ![s] = known_messages[s] \cup {x}]
    BY <2>1 DEF safe_acceptor_receives_message
  <2>kms. known_messages'[s] = known_messages[s] \cup {x}
          /\ \A t \in SafeAcceptors : t # s => known_messages'[t] = known_messages[t]
    BY <2>km, <1>inv DEF CInv
  <2>up. /\ Up \subseteq Messages
         /\ IsFiniteSet(Up)
         /\ \A z \in Up : Tran(z) \subseteq Up
         /\ Up \subseteq Msgs
    BY <2>1, <2>g, <1>inv, CUpGood
  <2>rmv. rm = CMMax(Up)
    BY <2>1, <2>g, <1>inv, CRMIsMax
  <2>upd. recent_messages' = CRecentUpdate(s, x)
    <3>A. CASE CWellFormed(cand)
      <4>cand. cand \in Messages /\ TranExclusive(cand) = Up /\ Sig(cand) = s
        BY <2>1, <2>g, <1>inv, <3>A, CCandFacts
      <4>msgs. Msgs' = Msgs \cup {cand}
        <5>3. (known_messages'[s] \cup {x}) \cup {m \in Msgs : Sig(m) = s} = CAT(s, x)
          BY <2>kms DEF CAT, CSelfSent
        <5>disj. \/ \E y \in {yy \in (Messages \ Proposals) :
                                Sig(yy) = s /\ TranExclusive(yy) = CAT(s, x)} :
                      Msgs' = Msgs \cup {y}
                 \/ ({yy \in (Messages \ Proposals) :
                        Sig(yy) = s /\ TranExclusive(yy) = CAT(s, x)} = {}
                     /\ Msgs' = Msgs)
          BY <2>1, <5>3 DEF safe_acceptor_receives_message
        <5>ne. {yy \in (Messages \ Proposals) :
                  Sig(yy) = s /\ TranExclusive(yy) = CAT(s, x)} # {}
          <6>1. \E y \in (Messages \ Proposals) :
                  Sig(y) = s /\ TranExclusive(y) = CAT(s, x)
            BY <3>A, <2>agree DEF CForcedSendAgreesAt
          <6> QED BY <6>1
        <5>y. PICK y \in {yy \in (Messages \ Proposals) :
                            Sig(yy) = s /\ TranExclusive(yy) = CAT(s, x)} :
                Msgs' = Msgs \cup {y}
          BY <5>disj, <5>ne
        <5>yw. y \in (Messages \ Proposals) /\ Sig(y) = s
                 /\ TranExclusive(y) = CAT(s, x)
          BY <5>y
        <5>can. y.priors = Refs(y)
          <6>1. y \in Msgs'  BY <5>y
          <6> QED BY <6>1, <5>yw, <2>1 DEF CSafeSentCanonical
        <5>eq. y = CCand(s, x)
          BY <5>yw, <5>can, <2>agree DEF CForcedSendAgreesAt
        <5> QED
          BY <5>y, <5>eq
      <4>self. \A t \in SafeAcceptors :
                 {m \in Msgs' : Sig(m) = t}
                   = IF t = s THEN CSelfSent(s) \cup {cand} ELSE CSelfSent(t)
        BY <4>msgs, <4>cand DEF CSelfSent
      <4>val. \A t \in SafeAcceptors :
                recent_messages'[t] = IF t = s THEN {cand} ELSE recent_messages[t]
        <5> SUFFICES ASSUME NEW t \in SafeAcceptors
                     PROVE  recent_messages'[t]
                              = IF t = s THEN {cand} ELSE recent_messages[t]
          OBVIOUS
        <5>1. CASE t = s
          <6>1. known_messages'[s] \cup {m \in Msgs' : Sig(m) = s} = Up \cup {cand}
            BY <2>kms, <4>self
          <6>2. CMMax(Up \cup {cand}) = {cand}
            BY <2>up, <4>cand, CMMaxAddTop
          <6> QED
            BY <5>1, <1>rok, <6>1, <6>2
        <5>2. CASE t # s
          <6>1. known_messages'[t] \cup {m \in Msgs' : Sig(m) = t}
                  = known_messages[t] \cup CSelfSent(t)
            BY <2>kms, <4>self, <5>2
          <6> QED
            BY <5>2, <1>rok, <6>1, <1>inv DEF CRecentIsMax, CSelfSent
        <5> QED
          BY <5>1, <5>2
      <4> QED
        BY <3>A, <4>val, <1>rok, <1>rtyp, <2>1 DEF CRecentUpdate
    <3>B. CASE ~CWellFormed(cand)
      <4>msgs. Msgs' = Msgs
        <5>1. ~(\E y \in (Messages \ Proposals) :
                  Sig(y) = s /\ TranExclusive(y) = CAT(s, x))
          BY <3>B, <2>agree DEF CForcedSendAgreesAt
        <5>2. (known_messages'[s] \cup {x}) \cup {m \in Msgs : Sig(m) = s} = CAT(s, x)
          BY <2>kms DEF CAT, CSelfSent
        <5> QED
          BY <2>1, <5>1, <5>2 DEF safe_acceptor_receives_message
      <4>val. \A t \in SafeAcceptors :
                recent_messages'[t] = IF t = s THEN rm ELSE recent_messages[t]
        <5> SUFFICES ASSUME NEW t \in SafeAcceptors
                     PROVE  recent_messages'[t]
                              = IF t = s THEN rm ELSE recent_messages[t]
          OBVIOUS
        <5>1. CASE t = s
          <6>1. known_messages'[s] \cup {m \in Msgs' : Sig(m) = s} = Up
            BY <2>kms, <4>msgs DEF CSelfSent
          <6> QED
            BY <5>1, <1>rok, <6>1, <2>rmv
        <5>2. CASE t # s
          <6>1. known_messages'[t] \cup {m \in Msgs' : Sig(m) = t}
                  = known_messages[t] \cup CSelfSent(t)
            BY <2>kms, <4>msgs, <5>2 DEF CSelfSent
          <6> QED
            BY <5>2, <1>rok, <6>1, <1>inv DEF CRecentIsMax, CSelfSent
        <5> QED
          BY <5>1, <5>2
      <4> QED
        BY <3>B, <4>val, <1>rok, <1>rtyp, <2>1 DEF CRecentUpdate
    <3> QED
      BY <3>A, <3>B
  <2>2. CSafeStep(<<s, x>>)
    <3>1. known_messages \in [SafeAcceptors -> SUBSET Messages]
      BY <1>inv DEF CInv
    <3> QED
      BY <2>1, <2>agree, <2>upd, <3>1, CSafeSentCanonical', CSafeStepEquiv
  <2> QED
    BY <2>1, <2>2 DEF CNext
<1>2. CASE \E self \in ByzSenders : byz(self)
  <2> PICK self \in ByzSenders : byz(self)
    BY <1>2
  <2>ns. self \notin SafeAcceptors
    BY DEF ByzSenders
  <2>km. known_messages' = known_messages
    BY DEF byz
  \* Only a non-safe sender's message was added, so no safe acceptor's
  \* self-sent set -- and hence no antichain -- moves.
  <2>self. \A t \in SafeAcceptors : {m \in Msgs' : Sig(m) = t} = CSelfSent(t)
    <3> PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
          Msgs' = Msgs \cup {y}
      BY DEF byz
    <3> QED
      BY <2>ns DEF CSelfSent
  <2>unch. recent_messages' = recent_messages
    <3> SUFFICES ASSUME NEW t \in SafeAcceptors
                 PROVE  recent_messages'[t] = recent_messages[t]
      BY <1>rok, <1>rtyp
    <3>1. known_messages'[t] \cup {m \in Msgs' : Sig(m) = t}
            = known_messages[t] \cup CSelfSent(t)
      BY <2>km, <2>self
    <3> QED
      BY <1>rok, <3>1, <1>inv DEF CRecentIsMax, CSelfSent
  <2>2. CByzStep(self)
    BY <2>unch, CByzEquiv
  <2> QED
    BY <2>2 DEF CNext
<1>3. CASE UNCHANGED vars
  <2>1. Msgs' = Msgs /\ known_messages' = known_messages
    BY <1>3 DEF vars
  <2>2. recent_messages' = recent_messages
    <3> SUFFICES ASSUME NEW t \in SafeAcceptors
                 PROVE  recent_messages'[t] = recent_messages[t]
      BY <1>rok, <1>rtyp
    <3> QED
      BY <1>rok, <2>1, <1>inv DEF CRecentIsMax, CSelfSent
  <2> QED
    BY <2>1, <2>2 DEF CVars
<1> QED
  BY <1>1, <1>2, <1>3 DEF Next
=============================================================================
