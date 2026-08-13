--------------------------- MODULE CSafeStepDTDef ---------------------------
\* CSafeStep, transcribed into disjunctive normal form: no IF, no LET, so
\* every primed variable is fixed by a LITERAL equation in each disjunct.
\*
\* This exists purely for ENABLED reasoning.  ExpandENABLED has to find a
\* witness for each primed variable, and it does that by matching v' = e
\* patterns; an IF-term straddling two branches (and a LET-bound `cand` inside
\* it) defeats the match.  CSafeStepDT says exactly what CSafeStep says --
\* CSafeStepDTEnabled discharges that -- but in the shape the witness search
\* wants.
\*
\* Definitions only, so that the three ExpandENABLED lemmas over it
\* (CSafeStepDTEnabled / CSafeStepDTSend / CSafeStepDTLearn) can each sit in a
\* module with a MINIMAL EXTENDS list.  That is not cosmetic: the witness
\* search is sensitive to ambient context, and the same BY that succeeds here
\* fails once a heavier module is in scope.
EXTENDS HPaxosPlusCalConcrete

CSafeStepDT(self) ==
  /\ self[2] \in Msgs
  /\ TranExclusive(self[2]) \subseteq known_messages[self[1]]
  /\ known_messages' = [known_messages EXCEPT
                          ![self[1]] = known_messages[self[1]] \cup {self[2]}]
  /\ \/ /\ CWellFormed(CCand(self[1], self[2]))
        /\ Msgs' = Msgs \cup {CCand(self[1], self[2])}
        /\ recent_messages' = [recent_messages EXCEPT
                                 ![self[1]] = {CCand(self[1], self[2])}]
     \/ /\ ~CWellFormed(CCand(self[1], self[2]))
        /\ Msgs' = Msgs
        /\ recent_messages' = [recent_messages EXCEPT
                                 ![self[1]] = CRM(self[1], self[2])]
=============================================================================
