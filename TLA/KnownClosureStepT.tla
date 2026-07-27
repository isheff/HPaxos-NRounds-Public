-------------------------- MODULE KnownClosureStepT --------------------------
EXTENDS HPaxosPlusCal, TranClosureExpanding

LEMMA KnownClosureStepT ==
  Inv /\ KnownTranClosureInvT /\ [Next]_vars => KnownTranClosureInvT'
<1> SUFFICES ASSUME Inv, KnownTranClosureInvT, [Next]_vars PROVE KnownTranClosureInvT'  OBVIOUS
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
      /\ (\A z \in Msgs : TranExclusive(z) \subseteq Msgs)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, KnownTranClosureInvT DEF KnownTranClosureInvT, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK pp \in SafeAcceptors \times Messages : safe_acceptor_receives_message(pp)  BY <1>3
  <2> DEFINE self == pp[1]
  <2> DEFINE x == pp[2]
  <2>2. /\ x \in Msgs
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
     BY <2>1 DEF safe_acceptor_receives_message
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>2, <1>i, <2>1a
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors PROVE TranClosure(known_messages'[s]) = known_messages'[s]
    BY DEF KnownTranClosureInvT
  <2>selfcase. CASE s = self
    <3>old. TranClosure(known_messages[self]) = known_messages[self]  BY KnownTranClosureInvT, <2>1a DEF KnownTranClosureInvT
    <3>1. TranClosure(known_messages[self] \cup {x}) = TranClosure(known_messages[self]) \cup TranClosure({x})
      BY DEF TranClosure
    <3>2. TranClosure({x}) = Tran(x)  BY DEF TranClosure
    <3>3. TranClosure(known_messages'[self]) = known_messages[self] \cup Tran(x)
      BY <2>kself, <3>1, <3>2, <3>old
    <3>4. Tran(x) = {x} \cup TranExclusive(x)  BY DEF Tran, TranExclusive
    <3>5. TranExclusive(x) \subseteq known_messages[self]  BY <2>2
    <3>6. Tran(x) \subseteq known_messages'[self]  BY <3>4, <3>5, <2>kself
    <3>7. TranClosure(known_messages'[self]) \subseteq known_messages'[self]
      BY <3>3, <3>6, <2>kself
    <3>8. known_messages'[self] \subseteq TranClosure(known_messages'[self])  BY TranClosureExpanding
    <3>9. TranClosure(known_messages'[self]) = known_messages'[self]  BY <3>7, <3>8
    <3> QED BY <3>9, <2>selfcase
  <2>othercase. CASE s # self
    <3>1. known_messages'[s] = known_messages[s]  BY <2>2, <2>othercase, <1>i, <2>1a
    <3> QED BY <3>1, KnownTranClosureInvT DEF KnownTranClosureInvT
  <2> QED BY <2>selfcase, <2>othercase
<1>4. CASE \E self \in ByzSenders : byz(self)
  <2>1. PICK self \in ByzSenders : byz(self)  BY <1>4
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2> QED BY <2>k, KnownTranClosureInvT DEF KnownTranClosureInvT
<1> QED BY <1>2, <1>3, <1>4 DEF Next
====================================================================
