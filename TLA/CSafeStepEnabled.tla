--------------------------- MODULE CSafeStepEnabled ---------------------------
\* ENABLED transfers from the abstract learn step to the concrete one, at every
\* state the joint invariant holds -- which, by CJointHolds, is every reachable
\* state of CSpec.
\*
\* This is the half of the correspondence that refinement does NOT give.
\* CSpec => Spec (CRefinesAbstract) says every concrete transition is an
\* abstract one, which transfers SAFETY.  Liveness needs the other direction at
\* the level of possibility: wherever HPaxosPlusCal could take a step,
\* HPaxosPlusCalConcrete can too.  Without it, a fairness assumption on the
\* concrete spec could be vacuous where the abstract one is not.
\*
\* The argument splits on the forced send, and the abstract action's own
\* nondeterminism is what makes the split clean:
\*
\*   - If a forced-send witness exists at all, the built candidate is well
\*     formed (CForcedSendAgreesAt), and among the witnesses there is always a
\*     CANONICAL one -- priors exactly Refs -- which is precisely the record
\*     the concrete step builds.  It has never been sent (CCandNotSent), so the
\*     concrete step grows Msgs.
\*   - If no witness exists, the abstract action pins Msgs' = Msgs, so the only
\*     way it could have been enabled in the angle-bracket sense is by growing
\*     known_messages -- and the concrete step grows known_messages the same
\*     way, by the same verbatim assignment.
EXTENDS HPaxosPlusCalConcrete, CAgreesFromJoint, CCandNotSent,
        CLearnEnabledChar, CSafeStepEnabledIntro, TLAPS

LEMMA CSafeStepEnabled ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption,
         CJoint,
         NEW self \in SafeAcceptors \X Messages,
         ENABLED <<safe_acceptor_receives_message(self)>>_vars
  PROVE  ENABLED <<CSafeStep(self)>>_CVars
<1>s. self[1] \in SafeAcceptors /\ self[2] \in Messages
  OBVIOUS
<1>typ. known_messages \in [SafeAcceptors -> SUBSET Messages]
  BY DEF CJoint, CInv
<1>ch. /\ self[2] \in Msgs
       /\ TranExclusive(self[2]) \subseteq known_messages[self[1]]
       /\ \/ \E y \in (Messages \ Proposals) :
                Sig(y) = self[1] /\ TranExclusive(y) = CAT(self[1], self[2])
          \/ self[2] \notin known_messages[self[1]]
  BY <1>typ, CLearnEnabledChar
<1>ag. CForcedSendAgreesAt(self[1], self[2])
  BY <1>s, <1>ch, CAgreesFromJoint
<1>d. \/ (/\ ~CWellFormed(CCand(self[1], self[2]))
          /\ self[2] \notin known_messages[self[1]])
      \/ (/\ CWellFormed(CCand(self[1], self[2]))
          /\ CCand(self[1], self[2]) \notin Msgs)
  <2>1. CASE CWellFormed(CCand(self[1], self[2]))
    <3>1. CCand(self[1], self[2]) \notin Msgs
      BY <2>1, <1>ag, CCandNotSent
    <3> QED
      BY <2>1, <3>1
  <2>2. CASE ~CWellFormed(CCand(self[1], self[2]))
    \* No candidate, no witness -- so the abstract step sent nothing, and the
    \* angle-bracket disequality it was granted can only have come from
    \* known_messages.
    <3>1. ~\E y \in (Messages \ Proposals) :
             Sig(y) = self[1] /\ TranExclusive(y) = CAT(self[1], self[2])
      BY <2>2, <1>ag DEF CForcedSendAgreesAt
    <3>2. self[2] \notin known_messages[self[1]]
      BY <3>1, <1>ch
    <3> QED
      BY <2>2, <3>2
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>ch, <1>d, <1>typ, CSafeStepEnabledIntro
=============================================================================
