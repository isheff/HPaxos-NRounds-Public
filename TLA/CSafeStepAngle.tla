--------------------------- MODULE CSafeStepAngle ---------------------------
\* A concrete safe-acceptor step that MOVES is an abstract one that moves.
\*
\* The action implication is CSafeStepEquiv's forward half.  What this adds is
\* the angle brackets: CVars carries recent_messages, which vars does not, so a
\* priori a concrete step could move CVars while leaving <<Msgs,
\* known_messages>> alone -- and then it would be a stutter for HPaxosPlusCal,
\* and the fairness transfer would break.  It cannot, and the reason is that
\* recent_messages moves only when one of the other two does:
\*
\*   - If the candidate is well formed the step sends it, and it has never been
\*     sent (CCandNotSent), so Msgs grows.
\*   - Otherwise nothing is sent, so a frozen Msgs and a frozen known_messages
\*     force self[2] to be already known -- and then CRM writes recent_messages
\*     back unchanged.  So CVars is frozen too, and there was no concrete step
\*     to speak of.
EXTENDS HPaxosPlusCalConcrete, CAgreesFromJoint, CCandNotSent,
        CSafeGuardsIdentical, CSafeStepEquiv, TLAPS

LEMMA CSafeStepAngle ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption,
         CJoint,
         NEW self \in SafeAcceptors \X Messages,
         <<CSafeStep(self)>>_CVars
  PROVE  <<safe_acceptor_receives_message(self)>>_vars
<1>s. self[1] \in SafeAcceptors /\ self[2] \in Messages
        /\ self = <<self[1], self[2]>>
  OBVIOUS
<1>step. CSafeStep(self) /\ CVars' # CVars
  OBVIOUS
<1>pair. CSafeStep(<<self[1], self[2]>>)
  BY <1>s, <1>step
<1>typ. known_messages \in [SafeAcceptors -> SUBSET Messages]
        /\ recent_messages \in [SafeAcceptors -> SUBSET Messages]
  BY DEF CJoint, CInv
<1>g. self[2] \in Msgs
        /\ TranExclusive(self[2]) \subseteq known_messages[self[1]]
  BY <1>pair, CSafeGuardsIdentical
<1>agree. CForcedSendAgreesAt(self[1], self[2])
  BY <1>s, <1>g, CAgreesFromJoint
\* The abstract action, from CSafeStepEquiv's forward half.
<1>abs. safe_acceptor_receives_message(self)
  <2>1. safe_acceptor_receives_message(<<self[1], self[2]>>)
    BY <1>s, <1>typ, <1>agree, <1>pair, CSafeStepEquiv
  <2> QED
    BY <1>s, <2>1
\* And the move: a frozen vars would freeze CVars too.
<1>move. vars' # vars
  <2> SUFFICES ASSUME vars' = vars
               PROVE  FALSE
    OBVIOUS
  <2>1. Msgs' = Msgs /\ known_messages' = known_messages
    BY DEF vars
  <2>km. known_messages'
           = [known_messages EXCEPT
                ![self[1]] = known_messages[self[1]] \cup {self[2]}]
    BY <1>step DEF CSafeStep
  <2>known. self[2] \in known_messages[self[1]]
    <3>1. known_messages'[self[1]] = known_messages[self[1]] \cup {self[2]}
      BY <2>km, <1>s, <1>typ
    <3> QED
      BY <3>1, <2>1
  <2>nwf. ~CWellFormed(CCand(self[1], self[2]))
    <3> SUFFICES ASSUME CWellFormed(CCand(self[1], self[2]))
                 PROVE  FALSE
      OBVIOUS
    <3>2. Msgs' = Msgs \cup {CCand(self[1], self[2])}
      BY <1>step DEF CSafeStep, CCand, CRM
    <3>3. CCand(self[1], self[2]) \notin Msgs
      BY <1>agree, CCandNotSent
    <3> QED
      BY <3>2, <3>3, <2>1
  <2>rm. CRM(self[1], self[2]) = recent_messages[self[1]]
    BY <2>known DEF CRM
  <2>rec. recent_messages'
            = [recent_messages EXCEPT ![self[1]] = CRM(self[1], self[2])]
    BY <1>step, <2>nwf DEF CSafeStep, CCand, CRM
  <2>same. recent_messages' = recent_messages
    <3>1. recent_messages'
            = [recent_messages EXCEPT ![self[1]] = recent_messages[self[1]]]
      BY <2>rec, <2>rm
    <3> QED
      BY <3>1, <1>s, <1>typ
  <2> QED
    BY <2>1, <2>same, <1>step DEF CVars
<1> QED
  BY <1>abs, <1>move
=============================================================================
