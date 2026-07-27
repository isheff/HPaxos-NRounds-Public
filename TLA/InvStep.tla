------------------------------ MODULE InvStep ------------------------------
\* FiniteSetTheorems supplies FS_AddElement.
EXTENDS HPaxosPlusCal, FiniteSetTheorems

LEMMA InvStep == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'  OBVIOUS
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
      /\ (\A z \in Msgs : TranExclusive(z) \subseteq Msgs)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, <1>i DEF Inv, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK p \in SafeAcceptors \times Messages : safe_acceptor_receives_message(p)  BY <1>3
  <2> DEFINE self == p[1]
  <2> DEFINE x == p[2]
  <2>2. /\ x \in Msgs
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
        /\ Msgs' = (LET T == (known_messages'[self] \cup {x})
                                  \cup {m \in Msgs : Sig(m) = self} IN
                       IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                         THEN Msgs \cup {CHOOSE y \in (Messages \ Proposals) :
                                             Sig(y) = self /\ TranExclusive(y) = T}
                         ELSE Msgs)
     BY <2>1 DEF safe_acceptor_receives_message
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>x. x \in Msgs /\ TranExclusive(x) \subseteq known_messages[self]  BY <2>2
  <2>k. known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]  BY <2>2
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>k, <1>i, <2>1a
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Msgs : Sig(m) = self}
  <2>tsub. T \subseteq Msgs
    <3>1. known_messages[self] \subseteq Msgs  BY <1>i, <2>1a
    <3>2. known_messages'[self] \subseteq Msgs  BY <2>kself, <3>1, <2>x
    <3>3. {m \in Msgs : Sig(m) = self} \subseteq Msgs  OBVIOUS
    <3> QED  BY <3>2, <3>3, <2>x
  <2>net. Msgs' = (IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                        THEN Msgs \cup {CHOOSE y \in (Messages \ Proposals) :
                                            Sig(y) = self /\ TranExclusive(y) = T}
                        ELSE Msgs)
     BY <2>2
  <2>ndisj. \/ Msgs' = Msgs
            \/ \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Msgs' = Msgs \cup {y}
    <3>1. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4> DEFINE y0 == CHOOSE y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
      <4>1. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = T  BY <3>1
      <4>2. Msgs' = Msgs \cup {y0}  BY <2>net, <3>1
      <4> QED  BY <4>1, <4>2
    <3>2. CASE ~(\E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T)
      BY <2>net, <3>2
    <3> QED  BY <3>1, <3>2
  <2>kp. known_messages' \in [SafeAcceptors -> SUBSET Messages]
         /\ (\A s \in SafeAcceptors : known_messages'[s] \subseteq Msgs')
    <3>net. Msgs \subseteq Msgs'  BY <2>ndisj
    <3>1. known_messages[self] \cup {x} \subseteq Messages  BY <1>i, <2>x, <2>1a
    <3>2. known_messages' \in [SafeAcceptors -> SUBSET Messages]  BY <2>k, <3>1, <1>i, <2>1a
    <3>3. ASSUME NEW s \in SafeAcceptors PROVE known_messages'[s] \subseteq Msgs'
      <4>1. CASE s = self  BY <4>1, <2>kself, <1>i, <2>x, <3>net
      <4>2. CASE s # self  BY <4>2, <2>k, <1>i, <3>net
      <4> QED  BY <4>1, <4>2
    <3> QED  BY <3>2, <3>3
  <2>np. Msgs' \in SUBSET Messages /\ IsFiniteSet(Msgs')
         /\ (\A z \in Msgs' : TranExclusive(z) \subseteq Msgs')
    <3>1. CASE Msgs' = Msgs
      BY <3>1, <1>i
    <3>2. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Msgs' = Msgs \cup {y}
      <4> PICK y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Msgs' = Msgs \cup {y}
        BY <3>2
      <4>1. Msgs' \in SUBSET Messages  BY <1>i
      <4>2. IsFiniteSet(Msgs')  BY <1>i, FS_AddElement
      <4>3. ASSUME NEW z \in Msgs' PROVE TranExclusive(z) \subseteq Msgs'
        <5>1. CASE z \in Msgs  BY <5>1, <1>i
        <5>2. CASE z = y  BY <5>2, <2>tsub
        <5> QED  BY <5>1, <5>2
      <4> QED  BY <4>1, <4>2, <4>3
    <3> QED  BY <2>ndisj, <3>1, <3>2
  <2> QED  BY <2>kp, <2>np DEF Inv
<1>4. CASE \E self \in ByzSenders : byz(self)
  <2>1. PICK self \in ByzSenders : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
              Msgs' = (Msgs \cup {y})
     BY <2>1 DEF byz
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2>y. y \in Messages /\ TranExclusive(y) \subseteq Msgs  BY <2>2
  <2>np. Msgs' \in SUBSET Messages /\ IsFiniteSet(Msgs')
         /\ (\A z \in Msgs' : TranExclusive(z) \subseteq Msgs')
    <3>1. Msgs' \in SUBSET Messages  BY <2>2, <2>y, <1>i
    <3>2. IsFiniteSet(Msgs')  BY <2>2, <1>i, FS_AddElement
    <3>3. ASSUME NEW z \in Msgs' PROVE TranExclusive(z) \subseteq Msgs'
      <4>1. CASE z \in Msgs  BY <4>1, <1>i, <2>2
      <4>2. CASE z = y  BY <4>2, <2>y, <2>2
      <4> QED  BY <4>1, <4>2, <2>2
    <3> QED  BY <3>1, <3>2, <3>3
  <2>kp. known_messages' \in [SafeAcceptors -> SUBSET Messages]
         /\ (\A s \in SafeAcceptors : known_messages'[s] \subseteq Msgs')
    <3>net. Msgs \subseteq Msgs'  BY <2>2
    <3> QED  BY <2>k, <1>i, <3>net
  <2> QED  BY <2>kp, <2>np DEF Inv
<1> QED  BY <1>2, <1>3, <1>4 DEF Next
====================================================================
