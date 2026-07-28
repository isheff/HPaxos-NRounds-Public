--------------------------- MODULE CJointSafeStep ---------------------------
\* The safe-acceptor step preserves the joint invariant.  The two branches are
\* the two branches of CSafeStep: the candidate is well formed and gets sent,
\* or it is not and nothing is added to Msgs.
\*
\* CRecentIsMax' is the interesting conjunct.  On a send, the message just sent
\* dominates the whole enlarged knowledge set, so the antichain collapses to it
\* (CMMaxAddTop); otherwise the antichain is what CRM computed (CRMIsMax).
EXTENDS HPaxosPlusCalConcrete, CUpGood, CRMIsMax, CCandFacts, CTranClosureAdd,
        CMMaxAddTop, FiniteSetTheorems, TLAPS

LEMMA CJointSafeStep ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption,
         CJoint,
         NEW s \in SafeAcceptors, NEW x \in Messages,
         CSafeStep(<<s, x>>)
  PROVE  CJoint'
<1> DEFINE Up   == (known_messages[s] \cup {x}) \cup CSelfSent(s)
<1> DEFINE rm   == CRM(s, x)
<1> DEFINE cand == CCand(s, x)
<1>inv. CInv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ CRecentIsMax
  BY DEF CJoint
<1>step. /\ x \in Msgs
         /\ TranExclusive(x) \subseteq known_messages[s]
         /\ known_messages' = [known_messages EXCEPT ![s] = known_messages[s] \cup {x}]
         /\ IF CWellFormed(cand)
              THEN /\ Msgs' = Msgs \cup {cand}
                   /\ recent_messages' = [recent_messages EXCEPT ![s] = {cand}]
              ELSE /\ Msgs' = Msgs
                   /\ recent_messages' = [recent_messages EXCEPT ![s] = rm]
  BY DEF CSafeStep, CRM, CCand
<1>up. /\ Up \subseteq Messages
       /\ IsFiniteSet(Up)
       /\ \A z \in Up : Tran(z) \subseteq Up
       /\ Up \subseteq Msgs
  BY <1>inv, <1>step, CUpGood
<1>rm. rm = CMMax(Up)
  BY <1>inv, <1>step, CRMIsMax
<1>rmsub. rm \subseteq Up /\ rm \subseteq Msgs /\ rm \subseteq Messages
  BY <1>rm, <1>up DEF CMMax
\* known_messages moves the same way in both branches.
<1>km. /\ known_messages'[s] = known_messages[s] \cup {x}
       /\ \A t \in SafeAcceptors : t # s => known_messages'[t] = known_messages[t]
       /\ known_messages' \in [SafeAcceptors -> SUBSET Messages]
       /\ \A t \in SafeAcceptors : known_messages'[t] \subseteq Msgs
  <2>1. s \in DOMAIN known_messages
    BY <1>inv DEF CInv
  <2> QED
    BY <1>inv, <1>step, <2>1 DEF CInv
<1>ktc. \A t \in SafeAcceptors : TranClosure(known_messages'[t]) = known_messages'[t]
  <2> SUFFICES ASSUME NEW t \in SafeAcceptors
               PROVE  TranClosure(known_messages'[t]) = known_messages'[t]
    OBVIOUS
  <2>1. CASE t = s
    <3>1. TranClosure(known_messages[s]) = known_messages[s]
      BY <1>inv DEF KnownTranClosureInvT
    <3>2. TranClosure(known_messages[s] \cup {x}) = known_messages[s] \cup {x}
      BY <1>step, <3>1, CTranClosureAdd
    <3> QED
      BY <2>1, <1>km, <3>2
  <2> QED
    BY <1>inv, <1>km, <2>1 DEF KnownTranClosureInvT
\* ---- branch 1: the candidate is well formed and gets sent ----
<1>A. CASE CWellFormed(cand)
  <2>cand. /\ cand \in Messages
           /\ TranExclusive(cand) = Up
           /\ Sig(cand) = s
    BY <1>inv, <1>step, <1>A, CCandFacts
  <2>msgs. Msgs' = Msgs \cup {cand}
    BY <1>step, <1>A
  <2>rec. /\ recent_messages'[s] = {cand}
          /\ \A t \in SafeAcceptors : t # s => recent_messages'[t] = recent_messages[t]
          /\ recent_messages' \in [SafeAcceptors -> SUBSET Messages]
    <3>1. s \in DOMAIN recent_messages
      BY <1>inv DEF CInv
    <3> QED
      BY <1>step, <1>A, <2>cand, <3>1, <1>inv DEF CInv
  <2>self. \A t \in SafeAcceptors :
             {m \in Msgs' : Sig(m) = t} = IF t = s THEN CSelfSent(s) \cup {cand}
                                                   ELSE CSelfSent(t)
    BY <2>msgs, <2>cand DEF CSelfSent
  <2>1. CInv'
    <3>1. Msgs' \in SUBSET Messages
      BY <2>msgs, <2>cand, <1>inv DEF CInv
    <3>2. IsFiniteSet(Msgs')
      BY <2>msgs, <1>inv, FS_AddElement DEF CInv
    <3>3. \A t \in SafeAcceptors : known_messages'[t] \subseteq Msgs'
      BY <1>km, <2>msgs
    <3>4. \A t \in SafeAcceptors : recent_messages'[t] \subseteq Msgs'
      <4> SUFFICES ASSUME NEW t \in SafeAcceptors
                   PROVE  recent_messages'[t] \subseteq Msgs'
        OBVIOUS
      <4>1. CASE t = s
        BY <4>1, <2>rec, <2>msgs
      <4> QED
        BY <4>1, <2>rec, <2>msgs, <1>inv DEF CInv
    <3>5. \A z \in Msgs' : TranExclusive(z) \subseteq Msgs'
      <4> SUFFICES ASSUME NEW z \in Msgs'
                   PROVE  TranExclusive(z) \subseteq Msgs'
        OBVIOUS
      <4>1. CASE z \in Msgs
        BY <4>1, <2>msgs, <1>inv DEF CInv
      <4>2. CASE z = cand
        BY <4>2, <2>cand, <1>up, <2>msgs
      <4> QED
        BY <2>msgs, <4>1, <4>2
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <1>km, <2>rec DEF CInv
  <2>2. SelfSentBoundedInvT'
    <3> SUFFICES ASSUME NEW t \in SafeAcceptors, NEW z \in Msgs', Sig(z) = t
                 PROVE  TranExclusive(z)
                          \subseteq known_messages'[t] \cup {m \in Msgs' : Sig(m) = t}
      BY DEF SelfSentBoundedInvT
    <3>1. CASE z \in Msgs
      <4>1. TranExclusive(z) \subseteq known_messages[t] \cup {m \in Msgs : Sig(m) = t}
        BY <3>1, <1>inv DEF SelfSentBoundedInvT
      <4>2. known_messages[t] \subseteq known_messages'[t]
        BY <1>km
      <4>3. {m \in Msgs : Sig(m) = t} \subseteq {m \in Msgs' : Sig(m) = t}
        BY <2>msgs
      <4> QED
        BY <4>1, <4>2, <4>3
    <3>2. CASE z = cand
      <4>1. t = s
        BY <3>2, <2>cand
      <4>2. TranExclusive(cand) = known_messages'[s] \cup CSelfSent(s)
        BY <2>cand, <1>km
      <4>3. CSelfSent(s) \subseteq {m \in Msgs' : Sig(m) = t}
        BY <4>1, <2>self
      <4> QED
        BY <3>2, <4>1, <4>2, <4>3
    <3> QED
      BY <2>msgs, <3>1, <3>2
  <2>3. CRecentIsMax'
    <3> SUFFICES ASSUME NEW t \in SafeAcceptors
                 PROVE  recent_messages'[t]
                          = CMMax(known_messages'[t] \cup {m \in Msgs' : Sig(m) = t})
      BY DEF CRecentIsMax, CSelfSent
    <3>1. CASE t = s
      <4>1. known_messages'[s] \cup {m \in Msgs' : Sig(m) = s} = Up \cup {cand}
        BY <1>km, <2>self
      <4>2. CMMax(Up \cup {cand}) = {cand}
        BY <1>up, <2>cand, CMMaxAddTop
      <4> QED
        BY <3>1, <2>rec, <4>1, <4>2
    <3>2. CASE t # s
      <4>1. known_messages'[t] \cup {m \in Msgs' : Sig(m) = t}
              = known_messages[t] \cup CSelfSent(t)
        BY <1>km, <2>self, <3>2
      <4> QED
        BY <3>2, <2>rec, <4>1, <1>inv DEF CRecentIsMax, CSelfSent
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>1, <2>2, <2>3, <1>ktc DEF CJoint, KnownTranClosureInvT
\* ---- branch 2: nothing is sent ----
<1>B. CASE ~CWellFormed(cand)
  <2>msgs. Msgs' = Msgs
    BY <1>step, <1>B
  <2>rec. /\ recent_messages'[s] = rm
          /\ \A t \in SafeAcceptors : t # s => recent_messages'[t] = recent_messages[t]
          /\ recent_messages' \in [SafeAcceptors -> SUBSET Messages]
    <3>1. s \in DOMAIN recent_messages
      BY <1>inv DEF CInv
    <3> QED
      BY <1>step, <1>B, <1>rmsub, <3>1, <1>inv DEF CInv
  <2>1. CInv'
    <3>1. \A t \in SafeAcceptors : recent_messages'[t] \subseteq Msgs'
      <4> SUFFICES ASSUME NEW t \in SafeAcceptors
                   PROVE  recent_messages'[t] \subseteq Msgs'
        OBVIOUS
      <4>1. CASE t = s
        BY <4>1, <2>rec, <2>msgs, <1>rmsub
      <4> QED
        BY <4>1, <2>rec, <2>msgs, <1>inv DEF CInv
    <3> QED
      BY <3>1, <2>msgs, <1>km, <2>rec, <1>inv DEF CInv
  <2>2. SelfSentBoundedInvT'
    <3> SUFFICES ASSUME NEW t \in SafeAcceptors, NEW z \in Msgs', Sig(z) = t
                 PROVE  TranExclusive(z)
                          \subseteq known_messages'[t] \cup {m \in Msgs' : Sig(m) = t}
      BY DEF SelfSentBoundedInvT
    <3>1. TranExclusive(z) \subseteq known_messages[t] \cup {m \in Msgs : Sig(m) = t}
      BY <2>msgs, <1>inv DEF SelfSentBoundedInvT
    <3> QED
      BY <3>1, <2>msgs, <1>km
  <2>3. CRecentIsMax'
    <3> SUFFICES ASSUME NEW t \in SafeAcceptors
                 PROVE  recent_messages'[t]
                          = CMMax(known_messages'[t] \cup {m \in Msgs' : Sig(m) = t})
      BY DEF CRecentIsMax, CSelfSent
    <3>1. CASE t = s
      <4>1. known_messages'[s] \cup {m \in Msgs' : Sig(m) = s} = Up
        BY <1>km, <2>msgs DEF CSelfSent
      <4> QED
        BY <3>1, <2>rec, <4>1, <1>rm
    <3>2. CASE t # s
      <4>1. known_messages'[t] \cup {m \in Msgs' : Sig(m) = t}
              = known_messages[t] \cup CSelfSent(t)
        BY <1>km, <2>msgs, <3>2 DEF CSelfSent
      <4> QED
        BY <3>2, <2>rec, <4>1, <1>inv DEF CRecentIsMax, CSelfSent
    <3> QED
      BY <3>1, <3>2
  <2> QED
    BY <2>1, <2>2, <2>3, <1>ktc DEF CJoint, KnownTranClosureInvT
<1> QED
  BY <1>A, <1>B
=============================================================================
