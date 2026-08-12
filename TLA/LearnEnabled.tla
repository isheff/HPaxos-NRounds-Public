---------------------------- MODULE LearnEnabled ----------------------------
\* ExpandENABLED comes from TLAPS. Per the skill, the ENABLED recipe wants a
\* deterministic action, and the forced send is now a nondeterministic choice
\* among witnesses.  So: determinize the choice with CHOOSE (DetSend), prove
\* ENABLED of that (the recipe applies verbatim), and transfer along the
\* action implication DetSend => safe_acceptor_receives_message -- with both
\* ENABLEDs expanded, the hypothesis existential Skolemizes into exactly the
\* witnesses the goal existential needs.
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* The forced send with the witness pinned by CHOOSE: one deterministic
\* refinement of the learn action.
DetSend(self) ==
  /\ self[2] \in Msgs
  /\ TranExclusive(self[2]) \subseteq known_messages[self[1]]
  /\ known_messages' = [known_messages EXCEPT
                          ![self[1]] = known_messages[self[1]] \cup {self[2]}]
  /\ Msgs' = LET T == (known_messages'[self[1]] \cup {self[2]})
                      \cup {m \in Msgs : Sig(m) = self[1]}
                 W == {y \in (Messages \ Proposals) :
                         Sig(y) = self[1] /\ TranExclusive(y) = T}
             IN IF W = {} THEN Msgs ELSE Msgs \cup {CHOOSE y \in W : TRUE}

\* ENABLED of the per-message learn action.
LEMMA LearnEnabled ==
  ASSUME NEW a \in SafeAcceptors, NEW x \in Msgs,
         TranExclusive(x) \subseteq known_messages[a],
         x \notin known_messages[a],
         known_messages \in [SafeAcceptors -> SUBSET Messages]
  PROVE  ENABLED <<safe_acceptor_receives_message(<<a, x>>)>>_vars
<1>det. ENABLED <<DetSend(<<a, x>>)>>_vars
  BY ExpandENABLED DEF DetSend, vars
<1>imp. ENABLED <<DetSend(<<a, x>>)>>_vars
          => ENABLED <<safe_acceptor_receives_message(<<a, x>>)>>_vars
  BY ExpandENABLED DEF DetSend, safe_acceptor_receives_message, vars
<1> QED BY <1>det, <1>imp
=============================================================================
