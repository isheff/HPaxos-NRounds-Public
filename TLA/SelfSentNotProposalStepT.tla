---------------------- MODULE SelfSentNotProposalStepT ----------------------
EXTENDS HPaxosPlusCal

LEMMA SelfSentNotProposalStepT ==
  Inv /\ SelfSentNotProposalInvT /\ [Next]_vars => SelfSentNotProposalInvT'
<1> SUFFICES ASSUME Inv, SelfSentNotProposalInvT, [Next]_vars PROVE SelfSentNotProposalInvT'  OBVIOUS
<1>2. CASE vars' = vars
  BY <1>2, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT, vars
<1>3. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
  <2>1. PICK pp \in SafeAcceptors \times Messages : safe_acceptor_receives_message(pp)  BY <1>3
  <2> DEFINE self == pp[1]
  <2> DEFINE x == pp[2]
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
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW z \in Msgs', Sig(z) = s
               PROVE ~IsProposal(z)
    BY DEF SelfSentNotProposalInvT
  <2>zcase. z \in Msgs \/ (\E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y)
    BY <2>ndisj
  <2>old. CASE z \in Msgs
    BY <2>old, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
  <2>new. CASE \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y
    <3> PICK y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T /\ z = y  BY <2>new
    <3>ynotprop. y \notin Proposals  OBVIOUS
    <3> QED BY <3>ynotprop DEF IsProposal
  <2> QED BY <2>zcase, <2>old, <2>new
<1>4. CASE \E self \in ByzSenders : byz(self)
  <2>1. PICK self \in ByzSenders : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
              Msgs' = (Msgs \cup {y})
     BY <2>1 DEF byz
  <2>selfnotsafe. self \notin SafeAcceptors  BY <2>1 DEF ByzSenders
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW z \in Msgs', Sig(z) = s
               PROVE ~IsProposal(z)
    BY DEF SelfSentNotProposalInvT
  <2>ynotsafe. z # y
    <3> SUFFICES ASSUME z = y PROVE FALSE  OBVIOUS
    <3>1. Sig(z) = self  BY <2>2
    <3> QED BY <3>1, <2>selfnotsafe
  <2>zold. z \in Msgs  BY <2>2, <2>ynotsafe
  <2> QED BY <2>zold, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
<1> QED BY <1>2, <1>3, <1>4 DEF Next
====================================================================
