----------------------------- MODULE OneBStepT -----------------------------
EXTENDS HPaxosPlusCal,
        InvStep, ChainStep, CaughtSMonoT, OneBConstructT, OneBAnyWitnessT

LEMMA OneBStepT ==
  MessageInterfaceAssumptions /\ LearnerGraphAssumptions /\ AcceptorsAssumptions /\
  Inv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ SelfSentNotProposalInvT /\
  SafeAcceptorChainInv /\ OneBInvariantT /\ [Next]_vars => OneBInvariantT'
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
                    Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
                    SafeAcceptorChainInv, OneBInvariantT, [Next]_vars
             PROVE OneBInvariantT'  OBVIOUS
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, OneBInvariantT DEF OneBInvariantT, vars
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
  <2>1a. self \in SafeAcceptors  BY <2>1
  <2>kself. known_messages'[self] = known_messages[self] \cup {x}  BY <2>2, <1>i, <2>1a
  <2>xmsg. x \in Messages  BY <2>2, <1>i
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Msgs : Sig(m) = self}
  <2> DEFINE TU == (known_messages[self] \cup {x}) \cup {m \in Msgs : Sig(m) = self}
  <2>tueqt. TU = T  BY <2>kself
  <2>net. \/ \E y \in {yy \in (Messages \ Proposals) :
                         Sig(yy) = self /\ TranExclusive(yy) = T} :
               Msgs' = Msgs \cup {y}
          \/ ({yy \in (Messages \ Proposals) :
                 Sig(yy) = self /\ TranExclusive(yy) = T} = {}
              /\ Msgs' = Msgs)
     BY <2>2
  <2>netmono. Msgs \subseteq Msgs'  BY <2>net
  <2>knownmono. \A ss \in SafeAcceptors : known_messages[ss] \subseteq known_messages'[ss]
    BY <2>2, <1>i, <2>1a
  <2>invp. Inv'  BY InvStep
  <2>chainp. SafeAcceptorChainInv'  BY ChainStep
  <2>uncp2. self \notin CaughtS(Msgs')
    <3> SUFFICES ASSUME self \in CaughtS(Msgs') PROVE FALSE  OBVIOUS
    <3>3. \E m1 \in Msgs' : \E m2 \in Msgs' :
            Sig(m1) = self /\ Sig(m2) = self /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY DEF CaughtS
    <3>4. PICK m1 \in Msgs' : \E m2 \in Msgs' :
            Sig(m1) = self /\ Sig(m2) = self /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY <3>3
    <3>5. PICK m2 \in Msgs' :
            Sig(m1) = self /\ Sig(m2) = self /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY <3>4
    <3>comp. m1 \in Tran(m2) \/ m2 \in Tran(m1)  BY <2>1a, <3>5, <2>chainp DEF SafeAcceptorChainInv
    <3> QED BY <3>comp, <3>5
  <2>tsub. T \subseteq Msgs'
    <3>1. known_messages'[self] \subseteq Msgs'  BY <2>invp DEF Inv
    <3>2. {m \in Msgs : Sig(m) = self} \subseteq Msgs  OBVIOUS
    <3>3. x \in known_messages'[self]  BY <2>kself
    <3> QED BY <3>1, <3>2, <3>3, <2>netmono
  <2>tcnet. TranClosure(T) \subseteq Msgs'
    <3> SUFFICES ASSUME NEW z \in TranClosure(T) PROVE z \in Msgs'  OBVIOUS
    <3>1. PICK w \in T : z \in Tran(w)  BY DEF TranClosure
    <3>2. w \in Msgs'  BY <3>1, <2>tsub
    <3>3. z = w \/ z \in TranExclusive(w)  BY <3>1 DEF Tran, TranExclusive
    <3>4. TranExclusive(w) \subseteq Msgs'  BY <3>2, <2>invp DEF Inv
    <3> QED BY <3>2, <3>3, <3>4
  <2>tuncaught. self \notin CaughtS(TranClosure(T))  BY <2>tcnet, <2>uncp2, CaughtSMonoT
  <2>tuncaughtU. self \notin CaughtS(TranClosure(TU))  BY <2>tuncaught, <2>tueqt
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW p \in known_messages'[s],
                      B(p) = b, IsProposal(p),
                      \A xx \in known_messages'[s] : IsProposal(xx) => B(xx) <= b
               PROVE \E oneb \in Msgs' : (B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb))
    BY DEF OneBInvariantT
  <2>scase. CASE s # self
    <3>keq. known_messages'[s] = known_messages[s]  BY <2>2, <2>scase, <1>i, <2>1a
    <3>pold. p \in known_messages[s]  BY <3>keq
    <3>bound. \A xx \in known_messages[s] : IsProposal(xx) => B(xx) <= b  BY <3>keq
    <3>old. \E oneb \in Msgs : (B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb))
      BY <3>pold, <3>bound, OneBInvariantT DEF OneBInvariantT
    <3> PICK oneb \in Msgs : B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb)  BY <3>old
    <3> QED BY <2>netmono
  <2>sceq. CASE s = self
    <3>oldcase. CASE p \in known_messages[self]
      <4>bound. \A xx \in known_messages[self] : IsProposal(xx) => B(xx) <= b
        BY <2>sceq, <2>kself
      <4>old. \E oneb \in Msgs : (B(oneb) = b /\ Sig(oneb) = self /\ IsOneB(oneb))
        BY <3>oldcase, <4>bound, OneBInvariantT DEF OneBInvariantT
      <4> PICK oneb \in Msgs : B(oneb) = b /\ Sig(oneb) = self /\ IsOneB(oneb)  BY <4>old
      <4> QED BY <2>netmono, <2>sceq
    <3>newcase. CASE p \notin known_messages[self]
      <4>pin. p \in known_messages'[self]  BY <2>sceq
      <4>peqx. p = x  BY <3>newcase, <2>kself, <4>pin
      <4>xprop. IsProposal(x)  BY <4>peqx
      <4>xbal. B(x) = b  BY <4>peqx
      <4>xnotknown. x \notin known_messages[self]  BY <3>newcase, <4>peqx
      <4>bound2. \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b
        <5> SUFFICES ASSUME NEW ww \in known_messages[self], IsProposal(ww) PROVE B(ww) <= b  OBVIOUS
        <5>1. ww \in known_messages'[self]  BY <2>kself
        <5>2. ww \in known_messages'[s]  BY <5>1, <2>sceq
        <5> QED BY <5>2
      <4>knowbcase. CASE \E ww \in known_messages[self] : IsProposal(ww) /\ B(ww) = b
        <5> PICK ww \in known_messages[self] : IsProposal(ww) /\ B(ww) = b  BY <4>knowbcase
        <5>bound3. \A xx \in known_messages[self] : IsProposal(xx) => B(xx) <= b  BY <4>bound2
        <5>old. \E oneb \in Msgs : (B(oneb) = b /\ Sig(oneb) = self /\ IsOneB(oneb))
          BY <5>bound3, OneBInvariantT DEF OneBInvariantT
        <5> PICK oneb \in Msgs : B(oneb) = b /\ Sig(oneb) = self /\ IsOneB(oneb)  BY <5>old
        <5> QED BY <2>netmono, <2>sceq
      <4>notknowbcase. CASE ~(\E ww \in known_messages[self] : IsProposal(ww) /\ B(ww) = b)
        <5>nb. \A ww \in known_messages[self] : IsProposal(ww) => B(ww) # b  BY <4>notknowbcase
        <5>exU. \E y \in (Messages \ Proposals) :
                 /\ Sig(y) = self
                 /\ TranExclusive(y) = TU
                 /\ B(y) = b
                 /\ IsOneB(y)
          BY <2>1a, <2>2, <2>xmsg, <4>xprop, <4>xbal, <4>xnotknown, <5>nb, <4>bound2, <2>tuncaughtU,
             OneBConstructT
        <5>ex. \E y \in (Messages \ Proposals) :
                 /\ Sig(y) = self
                 /\ TranExclusive(y) = T
                 /\ B(y) = b
                 /\ IsOneB(y)
          BY <5>exU, <2>tueqt
        <5>ifcond. \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
          BY <5>ex
        <5>wne. {yy \in (Messages \ Proposals) :
                   Sig(yy) = self /\ TranExclusive(yy) = T} # {}
          BY <5>ifcond
        <5>y0. PICK y0 \in {yy \in (Messages \ Proposals) :
                              Sig(yy) = self /\ TranExclusive(yy) = T} :
                 Msgs' = Msgs \cup {y0}
          BY <2>net, <5>wne
        <5>y0props. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = T
          BY <5>y0
        <5>y0propsU. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = TU
          BY <5>y0props, <2>tueqt
        <5>y0in. y0 \in Msgs'  BY <5>y0
        <5>y0any. B(y0) = b /\ IsOneB(y0)
          BY <2>1a, <2>2, <2>xmsg, <4>xprop, <4>xbal, <5>nb, <4>bound2, <5>y0propsU, OneBAnyWitnessT
        <5> QED BY <5>y0in, <5>y0props, <5>y0any, <2>sceq
      <4> QED BY <4>knowbcase, <4>notknowbcase
    <3> QED BY <3>oldcase, <3>newcase
  <2> QED BY <2>scase, <2>sceq
<1>4. CASE \E self \in ByzSenders : byz(self)
  <2>1. PICK self \in ByzSenders : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
              Msgs' = (Msgs \cup {y})
     BY <2>1 DEF byz
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2>netmono. Msgs \subseteq Msgs'  BY <2>2
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW p \in known_messages'[s],
                      B(p) = b, IsProposal(p),
                      \A xx \in known_messages'[s] : IsProposal(xx) => B(xx) <= b
               PROVE \E oneb \in Msgs' : (B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb))
    BY DEF OneBInvariantT
  <2>keq. known_messages'[s] = known_messages[s]  BY <2>k
  <2>pold. p \in known_messages[s]  BY <2>keq
  <2>bound. \A xx \in known_messages[s] : IsProposal(xx) => B(xx) <= b  BY <2>keq
  <2>old. \E oneb \in Msgs : (B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb))
    BY <2>pold, <2>bound, OneBInvariantT DEF OneBInvariantT
  <2> PICK oneb \in Msgs : B(oneb) = b /\ Sig(oneb) = s /\ IsOneB(oneb)  BY <2>old
  <2> QED BY <2>netmono
<1> QED BY <1>2, <1>3, <1>4 DEF Next
====================================================================
