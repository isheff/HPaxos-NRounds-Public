--------------------------- MODULE CNextProjects ---------------------------
\* Every concrete step is an abstract step.
\*
\* The forced-send agreement is only ever needed at pairs that pass the receive
\* guard -- which is all that can be established, since it rests on an
\* invariant about recent_messages that only speaks to enabled steps.
EXTENDS HPaxosPlusCalConcrete, CSafeStepEquiv, CByzEquiv, CSafeGuardsIdentical,
        TLAPS

LEMMA CNextProjects ==
  ASSUME known_messages \in [SafeAcceptors -> SUBSET Messages],
         \A s \in SafeAcceptors : \A x \in Messages :
           (x \in Msgs /\ TranExclusive(x) \subseteq known_messages[s])
             => CForcedSendAgreesAt(s, x),
         CNext
  PROVE  Next
<1>1. CASE \E self \in SafeAcceptors \times Messages : CSafeStep(self)
  <2> PICK self \in SafeAcceptors \times Messages : CSafeStep(self)
    BY <1>1
  <2>1. self[1] \in SafeAcceptors /\ self[2] \in Messages /\ self = <<self[1], self[2]>>
    OBVIOUS
  <2>g. self[2] \in Msgs
          /\ TranExclusive(self[2]) \subseteq known_messages[self[1]]
    BY <2>1, CSafeGuardsIdentical
  <2>2. CForcedSendAgreesAt(self[1], self[2])
    BY <2>1, <2>g
  <2>3. CSafeStep(<<self[1], self[2]>>)
    BY <2>1
  <2>4. safe_acceptor_receives_message(<<self[1], self[2]>>)
    BY <2>1, <2>2, <2>3, CSafeStepEquiv
  <2> QED
    BY <2>1, <2>4 DEF Next
<1>2. CASE \E self \in ByzSenders : CByzStep(self)
  <2> PICK self \in ByzSenders : CByzStep(self)
    BY <1>2
  <2>1. byz(self)
    BY CByzEquiv
  <2> QED
    BY <2>1 DEF Next
<1> QED
  BY <1>1, <1>2 DEF CNext
=============================================================================
