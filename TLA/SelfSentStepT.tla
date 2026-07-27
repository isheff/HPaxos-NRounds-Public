---------------------------- MODULE SelfSentStepT ----------------------------
EXTENDS HPaxosPlusCal

LEMMA SelfSentStepT ==
  Inv /\ SelfSentBoundedInvT /\ [Next]_vars => SelfSentBoundedInvT'
<1> SUFFICES ASSUME Inv, SelfSentBoundedInvT, [Next]_vars PROVE SelfSentBoundedInvT'  OBVIOUS
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
      /\ (\A z \in Msgs : TranExclusive(z) \subseteq Msgs)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, SelfSentBoundedInvT DEF SelfSentBoundedInvT, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK pp \in SafeAcceptors \times Messages : safe_acceptor_receives_message(pp)  BY <1>3
  <2> DEFINE self == pp[1]
  <2> DEFINE x == pp[2]
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
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>2, <1>i, <2>1a
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Msgs : Sig(m) = self}
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
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW z \in Msgs', Sig(z) = s
               PROVE TranExclusive(z) \subseteq known_messages'[s] \cup {m \in Msgs' : Sig(m) = s}
    BY DEF SelfSentBoundedInvT
  <2>netmono. Msgs \subseteq Msgs'  BY <2>ndisj
  <2>knownmono. known_messages[s] \subseteq known_messages'[s]  BY <2>2, <2>1a, <1>i
  <2>zcase. z \in Msgs \/ (\E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y)
    BY <2>ndisj
  <2>old. CASE z \in Msgs
    <3>old0. TranExclusive(z) \subseteq known_messages[s] \cup {m \in Msgs : Sig(m) = s}
      BY <2>old, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>sub. {m \in Msgs : Sig(m) = s} \subseteq {m \in Msgs' : Sig(m) = s}  BY <2>netmono
    <3> QED BY <3>old0, <3>sub, <2>knownmono
  <2>new. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y
    <3> PICK y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y  BY <2>new
    <3>seq. s = self  OBVIOUS
    <3>tez. TranExclusive(z) = T  OBVIOUS
    <3>tsub. {m \in Msgs : Sig(m) = self} \subseteq {m \in Msgs' : Sig(m) = self}  BY <2>netmono
    <3>tinT. T \subseteq known_messages'[self] \cup {m \in Msgs' : Sig(m) = self}  BY <3>tsub, <2>kself
    <3> QED BY <3>tez, <3>tinT, <3>seq
  <2> QED BY <2>zcase, <2>old, <2>new
<1>4. CASE \E self \in ByzSenders : byz(self)
  <2>1. PICK self \in ByzSenders : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
              Msgs' = (Msgs \cup {y})
     BY <2>1 DEF byz
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2>selfnotsafe. self \notin SafeAcceptors  BY <2>1 DEF ByzSenders
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW z \in Msgs', Sig(z) = s
               PROVE TranExclusive(z) \subseteq known_messages'[s] \cup {m \in Msgs' : Sig(m) = s}
    BY DEF SelfSentBoundedInvT
  <2>netmono. Msgs \subseteq Msgs'  BY <2>2
  <2>ynotsafe. z # y
    <3> SUFFICES ASSUME z = y PROVE FALSE  OBVIOUS
    <3>1. Sig(z) = self  BY <2>2
    <3> QED BY <3>1, <2>selfnotsafe
  <2>zold. z \in Msgs  BY <2>2, <2>ynotsafe
  <2>old0. TranExclusive(z) \subseteq known_messages[s] \cup {m \in Msgs : Sig(m) = s}
    BY <2>zold, SelfSentBoundedInvT DEF SelfSentBoundedInvT
  <2>sub. {m \in Msgs : Sig(m) = s} \subseteq {m \in Msgs' : Sig(m) = s}  BY <2>netmono
  <2> QED BY <2>old0, <2>sub, <2>k
<1> QED BY <1>2, <1>3, <1>4 DEF Next
====================================================================
