----------------------------- MODULE ChainStep -----------------------------
EXTENDS HPaxosPlusCal

LEMMA ChainStep ==
  Inv /\ SafeAcceptorChainInv /\ [Next]_vars => SafeAcceptorChainInv'
<1> SUFFICES ASSUME Inv, SafeAcceptorChainInv, [Next]_vars PROVE SafeAcceptorChainInv'  OBVIOUS
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
      /\ (\A z \in Msgs : TranExclusive(z) \subseteq Msgs)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2 DEF SafeAcceptorChainInv, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK p \in SafeAcceptors \times Messages : safe_acceptor_receives_message(p)  BY <1>3
  <2> DEFINE self == p[1]
  <2> DEFINE x == p[2]
  <2>2. /\ x \in Msgs
        /\ TranExclusive(x) \subseteq known_messages[self]
        /\ known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]
        /\ LET T == (known_messages'[self] \cup {x})
                    \cup {m \in Msgs : Sig(m) = self}
               W == {y \in (Messages \ Proposals) :
                       Sig(y) = self /\ TranExclusive(y) = T}
           IN \/ \E y \in W : Msgs' = Msgs \cup {y}
              \/ (W = {} /\ Msgs' = Msgs)
     BY <2>1 DEF safe_acceptor_receives_message
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>x. x \in Msgs /\ TranExclusive(x) \subseteq known_messages[self]  BY <2>2
  <2>k. known_messages' = [known_messages EXCEPT ![self] = known_messages[self] \cup {x}]  BY <2>2
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>k, <1>i, <2>1a
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Msgs : Sig(m) = self}
  <2>ndisj. \/ Msgs' = Msgs
            \/ \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Msgs' = Msgs \cup {y}
    <3>w. \/ \E y \in {yy \in (Messages \ Proposals) :
                         Sig(yy) = self /\ TranExclusive(yy) = T} :
               Msgs' = Msgs \cup {y}
          \/ ({yy \in (Messages \ Proposals) :
                 Sig(yy) = self /\ TranExclusive(yy) = T} = {}
              /\ Msgs' = Msgs)
      BY <2>2
    <3>1. CASE \E y \in {yy \in (Messages \ Proposals) :
                           Sig(yy) = self /\ TranExclusive(yy) = T} :
                 Msgs' = Msgs \cup {y}
      <4>1. PICK y \in {yy \in (Messages \ Proposals) :
                          Sig(yy) = self /\ TranExclusive(yy) = T} :
              Msgs' = Msgs \cup {y}
        BY <3>1
      <4> QED  BY <4>1
    <3>2. CASE ~(\E y \in {yy \in (Messages \ Proposals) :
                             Sig(yy) = self /\ TranExclusive(yy) = T} :
                   Msgs' = Msgs \cup {y})
      BY <3>w, <3>2
    <3> QED  BY <3>w, <3>1, <3>2
  <2>a. CASE Msgs' = Msgs
    BY <2>a DEF SafeAcceptorChainInv
  <2>b. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Msgs' = Msgs \cup {y}
    <3> PICK y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ Msgs' = Msgs \cup {y}
       BY <2>b
    <3>tsub2. {m \in Msgs : Sig(m) = self} \subseteq TranExclusive(y)  OBVIOUS
    <3>suf. SUFFICES ASSUME NEW s \in SafeAcceptors, NEW m1 \in Msgs', NEW m2 \in Msgs',
                        Sig(m1) = s, Sig(m2) = s
                 PROVE m1 \in Tran(m2) \/ m2 \in Tran(m1)
      BY DEF SafeAcceptorChainInv
    <3>m1. m1 \in Msgs \/ m1 = y  BY <3>suf
    <3>m2. m2 \in Msgs \/ m2 = y  BY <3>suf
    <3>case11. CASE m1 \in Msgs /\ m2 \in Msgs
      BY <3>case11, <3>suf DEF SafeAcceptorChainInv
    <3>case1y. CASE m1 \in Msgs /\ m2 = y
      <4>1. m1 \in {m \in Msgs : Sig(m) = self}  BY <3>case1y, <3>suf
      <4>2. m1 \in TranExclusive(y)  BY <4>1, <3>tsub2
      <4>3. m1 \in Tran(y)  BY <4>2 DEF TranExclusive
      <4> QED  BY <4>3, <3>case1y
    <3>casey1. CASE m1 = y /\ m2 \in Msgs
      <4>1. m2 \in {m \in Msgs : Sig(m) = self}  BY <3>casey1, <3>suf
      <4>2. m2 \in TranExclusive(y)  BY <4>1, <3>tsub2
      <4>3. m2 \in Tran(y)  BY <4>2 DEF TranExclusive
      <4> QED  BY <4>3, <3>casey1
    <3>caseyy. CASE m1 = y /\ m2 = y
      <4>1. m1 \in Tran(m1)  BY DEF Tran
      <4> QED  BY <4>1, <3>caseyy
    <3> QED BY <3>case11, <3>case1y, <3>casey1, <3>caseyy, <3>m1, <3>m2
  <2> QED BY <2>ndisj, <2>a, <2>b
<1>4. CASE \E self \in ByzSenders : byz(self)
  <2>1. PICK self \in ByzSenders : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
              Msgs' = (Msgs \cup {y})
     BY <2>1 DEF byz
  <2>selfnotsafe. self \notin SafeAcceptors  BY <2>1 DEF ByzSenders
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW m1 \in Msgs', NEW m2 \in Msgs',
                      Sig(m1) = s, Sig(m2) = s
               PROVE m1 \in Tran(m2) \/ m2 \in Tran(m1)
    BY DEF SafeAcceptorChainInv
  <2>m1. m1 \in Msgs \/ m1 = y  BY <2>2
  <2>m2. m2 \in Msgs \/ m2 = y  BY <2>2
  <2>m1net. m1 \in Msgs
    <3> SUFFICES ASSUME m1 = y PROVE FALSE  BY <2>m1
    <3> QED BY <2>selfnotsafe
  <2>m2net. m2 \in Msgs
    <3> SUFFICES ASSUME m2 = y PROVE FALSE  BY <2>m2
    <3> QED BY <2>selfnotsafe
  <2> QED BY <2>m1net, <2>m2net DEF SafeAcceptorChainInv
<1> QED BY <1>2, <1>3, <1>4 DEF Next
====================================================================
