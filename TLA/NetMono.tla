------------------------------ MODULE NetMono ------------------------------
EXTENDS HPaxosPlusCal

\* Msgs only grows.
LEMMA NetMono == [Next]_vars => Msgs \subseteq Msgs'
<1>1. CASE vars' = vars  BY <1>1 DEF vars
<1>2. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2> PICK self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)  BY <1>2
  <2> QED  BY DEF safe_acceptor_receives_message
<1>3. CASE \E self \in ByzSenders : byz(self)
  <2> PICK self \in ByzSenders : byz(self)  BY <1>3
  <2> QED  BY DEF byz
<1> QED  BY <1>1, <1>2, <1>3 DEF Next
====================================================================
