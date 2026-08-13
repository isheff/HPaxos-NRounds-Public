------------------------- MODULE CLearnEnabledChar -------------------------
\* What ENABLED of the ABSTRACT learn step gives us, as a state predicate.
\*
\* The two guards are read straight off the action.  The third conjunct is the
\* content: a learn step can only MOVE <<Msgs, known_messages>> in two ways --
\* it sends a forced-send witness, or it adds self[2] to known_messages.  When
\* no witness exists the abstract action pins Msgs' = Msgs, so the only room
\* left for the angle-bracket disequality is known_messages, and that needs
\* self[2] to be new to known_messages[self[1]].
\*
\* The abstract action's own T is written over known_messages', which the step
\* fixes to known_messages[self[1]] \cup {self[2]}; that makes it exactly
\* CAT(self[1], self[2]), the concrete side's name for the same set.
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CLearnEnabledChar ==
  ASSUME NEW self \in SafeAcceptors \X Messages,
         known_messages \in [SafeAcceptors -> SUBSET Messages],
         ENABLED <<safe_acceptor_receives_message(self)>>_vars
  PROVE  /\ self[2] \in Msgs
         /\ TranExclusive(self[2]) \subseteq known_messages[self[1]]
         /\ \/ \E y \in (Messages \ Proposals) :
                 Sig(y) = self[1] /\ TranExclusive(y) = CAT(self[1], self[2])
            \/ self[2] \notin known_messages[self[1]]
<1>s. self[1] \in SafeAcceptors /\ self[2] \in Messages
  OBVIOUS
\* Re-receipt leaves known_messages standing still: the EXCEPT writes back the
\* value that is already there.  Stated separately because it is the one place
\* the disequality has to be pushed through a function update.
<1>ex. self[2] \in known_messages[self[1]]
         => [known_messages EXCEPT
               ![self[1]] = known_messages[self[1]] \cup {self[2]}]
              = known_messages
  <2> SUFFICES ASSUME self[2] \in known_messages[self[1]]
               PROVE  [known_messages EXCEPT
                         ![self[1]] = known_messages[self[1]] \cup {self[2]}]
                        = known_messages
    OBVIOUS
  <2>1. known_messages[self[1]] \cup {self[2]} = known_messages[self[1]]
    OBVIOUS
  <2>2. [known_messages EXCEPT ![self[1]] = known_messages[self[1]]]
          = known_messages
    BY <1>s
  <2> QED
    BY <2>1, <2>2
<1> QED
  BY <1>s, <1>ex, ExpandENABLED
  DEF safe_acceptor_receives_message, vars, CAT, CSelfSent
=============================================================================
