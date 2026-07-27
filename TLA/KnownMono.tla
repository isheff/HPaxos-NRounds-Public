----------------------------- MODULE KnownMono -----------------------------
EXTENDS HPaxosPlusCal

\* Each known_messages[s] only grows.
LEMMA KnownMono ==
  Inv /\ [Next]_vars => \A s \in SafeAcceptors : known_messages[s] \subseteq known_messages'[s]
<1> SUFFICES ASSUME Inv, [Next]_vars, NEW s \in SafeAcceptors
             PROVE known_messages[s] \subseteq known_messages'[s]  OBVIOUS
<1>i. known_messages \in [SafeAcceptors -> SUBSET Messages]  BY DEF Inv
<1>1. CASE vars' = vars  BY <1>1 DEF vars
<1>2. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2> PICK self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)  BY <1>2
  <2>2. known_messages' = [known_messages EXCEPT ![self[1]] = known_messages[self[1]] \cup {self[2]}]
    BY DEF safe_acceptor_receives_message
  <2>3. CASE s = self[1]  BY <2>3, <2>2, <1>i
  <2>4. CASE s # self[1]  BY <2>4, <2>2, <1>i
  <2> QED  BY <2>3, <2>4
<1>3. CASE \E self \in ByzSenders : byz(self)
  <2> PICK self \in ByzSenders : byz(self)  BY <1>3
  <2> QED  BY DEF byz
<1> QED  BY <1>1, <1>2, <1>3 DEF Next
====================================================================
