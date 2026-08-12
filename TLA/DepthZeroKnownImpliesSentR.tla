--------------------- MODULE DepthZeroKnownImpliesSentR ---------------------
EXTENDS HPaxosPlusCal, BBallot, TranClosureExpanding,
        CaughtSAddNonAcceptor, FreshDef,
        SelfKnownClassifiedRW, OneBConstructBoundedRW, DecideableProposalOneBFreshRW,
        InitInv, InvStep, InitKnownClosureT, KnownClosureStepT,
        InitSelfSentT, SelfSentStepT, InitSelfSentNotProposalT, SelfSentNotProposalStepT,
        InitChain, ChainStep, ChainImpliesUncaught
LOCAL INSTANCE TLAPS

\* Relaxed Step-5 inductive invariant: once live acceptor a knows p, a has
\* already sent a ballot-B(p) depth-0 (fresh for alpha) message -- now under
\* the relaxed hypotheses (DPTE(m) merely inside Tran(p); other >bal proposals
\* allowed below B(p) with value V(p); connectivity preserved between the
\* <=bal view and the <B(p) view).
LEMMA DepthZeroKnownImpliesSentR ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions, ValueInterfaceAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         \A x \in TranClosure(m) : B(x) <= bal,
         NEW p \in Proposals,
         DecideableProposalTranExclusive(m) \subseteq Tran(p),
         B(p) > bal,
         Sig(p) \notin Acceptors,
         V(p) = DecideableProposalV(alpha, bal, m),
         NEW am \in SUBSET Messages,
         ConFromCaught(alpha, CaughtS({ww \in am : B(ww) < B(p)}))
           = ConFromCaught(alpha, CaughtS(TranClosure(m))),
         []HighNowT(p, bal),
         []LowNowT(bal, m),
         []AmNowT(am),
         NEW a \in LiveAcceptors
  PROVE Spec => [](p \in known_messages[a] =>
                     \E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
<1>a. a \in SafeAcceptors  BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
<1>aacc. a \in Acceptors  BY <1>a DEF AcceptorsAssumptions, SafeAcceptorsAssumption
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal /\ TranAcyclic
  BY DEF MessageInterfaceAssumptions
<1>hi0. HighNowT(p, bal)  BY PTL
<1>high. \A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
           ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))
  BY <1>hi0 DEF HighNowT
<1>lo0. LowNowT(bal, m)  BY PTL
<1>low. \A w \in Messages : ((w \in Msgs) /\ (B(w) <= bal)) => w \in m
  BY <1>lo0 DEF LowNowT
<1>am0. AmNowT(am)  BY PTL
<1>amn. \A xx : (xx \in Msgs) => (xx \in am)
  BY <1>am0 DEF AmNowT
<1>initt. Init => DZInvT(alpha, p, a)
  <2> SUFFICES ASSUME Init PROVE DZInvT(alpha, p, a)  BY DEF DZInvT
  <2> USE DEF DZInvT
  <2>1. known_messages = [s \in SafeAcceptors |-> {}]  BY DEF Init
  <2>2. known_messages[a] = {}  BY <2>1, <1>a
  <2> QED BY <2>2
<1>step. DZInvT(alpha, p, a)
         /\ (Inv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT
             /\ SelfSentNotProposalInvT /\ SafeAcceptorsUncaughtInvariant)
         /\ [Next]_vars
         => (DZInvT(alpha, p, a))'
  <2> SUFFICES ASSUME DZInvT(alpha, p, a), Inv, KnownTranClosureInvT, SelfSentBoundedInvT,
                      SelfSentNotProposalInvT, SafeAcceptorsUncaughtInvariant,
                      [Next]_vars
               PROVE (DZInvT(alpha, p, a))'
    OBVIOUS
  <2> USE DEF DZInvT
  <2> DEFINE Q == \E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)
  <2>i. /\ Msgs \in SUBSET Messages
        /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
        /\ IsFiniteSet(Msgs)
        /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
    BY DEF Inv
  <2>case. CASE p \in known_messages'[a]
    <3>nextcase. CASE \E self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)
      <4> PICK self \in SafeAcceptors \times Messages : safe_acceptor_receives_message(self)  BY <3>nextcase
      <4> DEFINE self1 == self[1]
      <4> DEFINE self2 == self[2]
      <4>eff. /\ self2 \in Msgs
              /\ TranExclusive(self2) \subseteq known_messages[self1]
              /\ known_messages' = [known_messages EXCEPT ![self1] = known_messages[self1] \cup {self2}]
              /\ LET T == (known_messages'[self1] \cup {self2})
                          \cup {mm \in Msgs : Sig(mm) = self1}
                     W == {y \in (Messages \ Proposals) :
                             Sig(y) = self1 /\ TranExclusive(y) = T}
                 IN \/ \E y \in W : Msgs' = Msgs \cup {y}
                    \/ (W = {} /\ Msgs' = Msgs)
        BY DEF safe_acceptor_receives_message
      <4>self1a. self1 \in SafeAcceptors  OBVIOUS
      <4>selfcase. CASE self1 = a /\ self2 = p
        <5>oldcase. CASE p \in known_messages[a]
          <6>q. Q  BY <5>oldcase
          <6>net. Msgs \subseteq Msgs'  BY <4>eff, <4>selfcase
          <6> QED BY <6>q, <6>net
        <5>newcase. CASE p \notin known_messages[a]
          <6>tep. TranExclusive(p) \subseteq known_messages[a]  BY <4>eff, <4>selfcase
          <6>kself. known_messages'[a] = known_messages[a] \cup {p}
            BY <4>eff, <4>selfcase, <2>i, <1>a
          <6>skhyp. SelfKnownHypR(a, p, bal)
            <7>1. B(p) > bal  OBVIOUS
            <7>2. p \notin known_messages[a]  BY <5>newcase
            <7>3. \A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
                    ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))  BY <1>high
            <7> QED BY <7>1, <7>2, <7>3 DEF SelfKnownHypR
          <6>class. \A w \in (known_messages[a] \cup {mm \in Msgs : Sig(mm) = a}) :
                      (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p)))
            BY <1>a, <6>skhyp, SelfKnownClassifiedRW
          <6>bpnat. B(p) \in Ballots
            <7>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
            <7> QED BY <7>pmsg, <1>mi, BBallot
          <6>balnat. bal \in Nat  BY DEF Ballots
          <6>bb1. \A ww \in known_messages[a] : IsProposal(ww) => B(ww) # B(p)
            <7> SUFFICES ASSUME NEW ww \in known_messages[a], IsProposal(ww) PROVE B(ww) # B(p)  OBVIOUS
            <7>w. ww \in (known_messages[a] \cup {mm \in Msgs : Sig(mm) = a})  OBVIOUS
            <7>cl. (B(ww) <= bal) \/ ((B(ww) < B(p)) /\ (V(ww) = V(p)))  BY <7>w, <6>class
            <7>wwmsg. ww \in Messages  BY <2>i, <1>a
            <7>wwnat. B(ww) \in Ballots  BY <7>wwmsg, <1>mi, BBallot
            <7> QED BY <7>cl, <7>wwnat, <6>bpnat, <6>balnat DEF Ballots
          <6>bb2. \A ww \in known_messages[a] : IsProposal(ww) => B(ww) <= B(p)
            <7> SUFFICES ASSUME NEW ww \in known_messages[a], IsProposal(ww) PROVE B(ww) <= B(p)  OBVIOUS
            <7>w. ww \in (known_messages[a] \cup {mm \in Msgs : Sig(mm) = a})  OBVIOUS
            <7>cl. (B(ww) <= bal) \/ ((B(ww) < B(p)) /\ (V(ww) = V(p)))  BY <7>w, <6>class
            <7>wwmsg. ww \in Messages  BY <2>i, <1>a
            <7>wwnat. B(ww) \in Ballots  BY <7>wwmsg, <1>mi, BBallot
            <7> QED BY <7>cl, <7>wwnat, <6>bpnat, <6>balnat DEF Ballots
          <6>unc. a \notin CaughtS(TranClosure((known_messages[a] \cup {p})
                                                \cup {mm \in Msgs : Sig(mm) = a}))
            <7>sub. TranClosure((known_messages[a] \cup {p}) \cup {mm \in Msgs : Sig(mm) = a})
                      \subseteq Msgs
              <8> SUFFICES ASSUME NEW z \in TranClosure((known_messages[a] \cup {p})
                                                          \cup {mm \in Msgs : Sig(mm) = a})
                           PROVE z \in Msgs  OBVIOUS
              <8>1. PICK w \in ((known_messages[a] \cup {p}) \cup {mm \in Msgs : Sig(mm) = a}) :
                      z \in Tran(w)  BY DEF TranClosure
              <8>2. z = w \/ z \in TranExclusive(w)  BY <8>1 DEF Tran, TranExclusive
              <8>3. w \in Msgs
                <9>1. CASE w \in known_messages[a]  BY <9>1, <2>i, <1>a
                <9>2. CASE w = p  BY <9>2, <4>eff, <4>selfcase
                <9>3. CASE w \in {mm \in Msgs : Sig(mm) = a}  BY <9>3
                <9> QED BY <8>1, <9>1, <9>2, <9>3
              <8>4. TranExclusive(w) \subseteq Msgs  BY <8>3 DEF Inv
              <8> QED BY <8>2, <8>3, <8>4
            <7>caughtmono. CaughtS(TranClosure((known_messages[a] \cup {p})
                                                \cup {mm \in Msgs : Sig(mm) = a}))
                              \subseteq CaughtS(Msgs)
              BY <7>sub DEF CaughtS
            <7>auncaught. a \notin CaughtS(Msgs)  BY <1>a DEF SafeAcceptorsUncaughtInvariant
            <7> QED BY <7>caughtmono, <7>auncaught
          <6>cbhyp. OneBCBHypR(a, p, bal)
            <7>1. TranExclusive(p) \subseteq known_messages[a]  BY <6>tep
            <7>2. p \notin known_messages[a]  BY <5>newcase
            <7>3. \A ww \in known_messages[a] : IsProposal(ww) => B(ww) # B(p)  BY <6>bb1
            <7>4. \A ww \in known_messages[a] : IsProposal(ww) => B(ww) <= B(p)  BY <6>bb2
            <7>5. a \notin CaughtS(TranClosure((known_messages[a] \cup {p})
                                                \cup {mm \in Msgs : Sig(mm) = a}))  BY <6>unc
            <7>6. B(p) > bal  OBVIOUS
            <7>7. \A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
                    ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))  BY <1>high
            <7> QED BY <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7 DEF OneBCBHypR
          <6>ex. \E known \in SUBSET Messages :
                   /\ known \subseteq Msgs
                   /\ a \notin CaughtS(TranClosure(known \cup {p}))
                   /\ (\A w \in known : (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p))))
                   /\ \E y \in (Messages \ Proposals) :
                        /\ Sig(y) = a
                        /\ TranExclusive(y) = TranClosure(known \cup {p})
                        /\ TranExclusive(y) = (known_messages[a] \cup {p}) \cup {mm \in Msgs : Sig(mm) = a}
                        /\ B(y) = B(p)
                        /\ IsOneB(y)
            BY <1>a, <6>cbhyp, OneBConstructBoundedRW
          <6> PICK known \in SUBSET Messages :
                /\ known \subseteq Msgs
                /\ a \notin CaughtS(TranClosure(known \cup {p}))
                /\ (\A w \in known : (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p))))
                /\ \E y \in (Messages \ Proposals) :
                     /\ Sig(y) = a
                     /\ TranExclusive(y) = TranClosure(known \cup {p})
                     /\ TranExclusive(y) = (known_messages[a] \cup {p}) \cup {mm \in Msgs : Sig(mm) = a}
                     /\ B(y) = B(p)
                     /\ IsOneB(y)
            BY <6>ex
          <6> PICK y \in (Messages \ Proposals) :
                /\ Sig(y) = a
                /\ TranExclusive(y) = TranClosure(known \cup {p})
                /\ TranExclusive(y) = (known_messages[a] \cup {p}) \cup {mm \in Msgs : Sig(mm) = a}
                /\ B(y) = B(p)
                /\ IsOneB(y)
            OBVIOUS
          <6>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
          <6>knownmsgs. known \subseteq Messages  BY <2>i
          <6>tceq. TranClosure(known \cup {p}) = (known_messages[a] \cup {p}) \cup {mm \in Msgs : Sig(mm) = a}
            OBVIOUS
          <6>tcl. \A w \in TranClosure(known \cup {p}) :
                    (w # p) => (\/ ((B(w) <= bal) /\ (w \in TranClosure(m)))
                                \/ ((B(w) > bal) /\ (B(w) < B(p)) /\ (V(w) = V(p))))
            <7> SUFFICES ASSUME NEW w \in TranClosure(known \cup {p}), w # p
                         PROVE \/ ((B(w) <= bal) /\ (w \in TranClosure(m)))
                               \/ ((B(w) > bal) /\ (B(w) < B(p)) /\ (V(w) = V(p)))
              OBVIOUS
            <7>win. w \in (known_messages[a] \cup {mm \in Msgs : Sig(mm) = a})  BY <6>tceq
            <7>cl. (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p)))  BY <7>win, <6>class
            <7>wnet. w \in Msgs  BY <7>win, <2>i, <1>a
            <7>wmsg. w \in Messages  BY <7>wnet, <2>i
            <7>bwnat. B(w) \in Ballots  BY <7>wmsg, <1>mi, BBallot
            <7>split. (B(w) <= bal) \/ (B(w) > bal)  BY <7>bwnat, <6>balnat DEF Ballots
            <7>c1. CASE B(w) <= bal
              <8>wm. w \in m  BY <7>wnet, <7>wmsg, <7>c1, <1>low
              <8>wtc. w \in TranClosure(m)  BY <8>wm, TranClosureExpanding
              <8> QED BY <7>c1, <8>wtc
            <7>c2. CASE B(w) > bal
              <8>notlow. ~(B(w) <= bal)  BY <7>c2, <7>bwnat, <6>balnat DEF Ballots
              <8>cl2. (B(w) < B(p)) /\ (V(w) = V(p))  BY <7>cl, <8>notlow
              <8> QED BY <7>c2, <8>cl2
            <7> QED BY <7>split, <7>c1, <7>c2
          <6>hs. \A w \in TranClosure(known \cup {p}) :
                   (w # p) => w \in {ww \in am : B(ww) < B(p)}
            <7> SUFFICES ASSUME NEW w \in TranClosure(known \cup {p}), w # p
                         PROVE w \in {ww \in am : B(ww) < B(p)}
              OBVIOUS
            <7>win. w \in (known_messages[a] \cup {mm \in Msgs : Sig(mm) = a})  BY <6>tceq
            <7>cl. (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p)))  BY <7>win, <6>class
            <7>wnet. w \in Msgs  BY <7>win, <2>i, <1>a
            <7>wam. w \in am  BY <7>wnet, <1>amn
            <7>wmsg. w \in Messages  BY <7>wnet, <2>i
            <7>bwnat. B(w) \in Ballots  BY <7>wmsg, <1>mi, BBallot
            <7>blt. B(w) < B(p)
              <8>c1. CASE B(w) <= bal
                BY <8>c1, <7>bwnat, <6>bpnat, <6>balnat DEF Ballots
              <8>c2. CASE (B(w) < B(p)) /\ (V(w) = V(p))  BY <8>c2
              <8> QED BY <7>cl, <8>c1, <8>c2
            <7> QED BY <7>wam, <7>blt
          <6>pin. p \in TranClosure(known \cup {p})
            <7>1. p \in Tran(p)  BY DEF Tran
            <7> QED BY <7>1 DEF TranClosure
          <6>closeq. TranClosure(known \cup {p}) = (TranClosure(known \cup {p}) \ {p}) \cup {p}
            BY <6>pin
          <6>minmsgs. (TranClosure(known \cup {p}) \ {p}) \in SUBSET Messages
            <7> SUFFICES ASSUME NEW z \in TranClosure(known \cup {p}) \ {p} PROVE z \in Messages  OBVIOUS
            <7>1. z \in (known_messages[a] \cup {p}) \cup {mm \in Msgs : Sig(mm) = a}  BY <6>tceq
            <7> QED BY <7>1, <2>i, <1>a, <6>pmsg
          <6>csmA. CaughtS(TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup {p}) \ {p})
            <7>1. CaughtS((TranClosure(known \cup {p}) \ {p}) \cup {p})
                    = CaughtS(TranClosure(known \cup {p}) \ {p})
              BY <1>mi, <6>minmsgs, CaughtSAddNonAcceptor
            <7> QED BY <7>1, <6>closeq
          <6>csmB. CaughtS(TranClosure(known \cup {p}) \ {p}) \subseteq CaughtS({ww \in am : B(ww) < B(p)})
            <7>sub. (TranClosure(known \cup {p}) \ {p}) \subseteq {ww \in am : B(ww) < B(p)}
              BY <6>hs
            <7> QED BY <7>sub DEF CaughtS
          <6>cs2. CaughtS(TranClosure(known \cup {p})) \subseteq CaughtS({ww \in am : B(ww) < B(p)})
            BY <6>csmA, <6>csmB
          <6> DEFINE T == (known_messages'[a] \cup {p}) \cup {mm \in Msgs : Sig(mm) = a}
          <6>Teq. T = TranClosure(known \cup {p})
            <7>1. T = (known_messages[a] \cup {p}) \cup {mm \in Msgs : Sig(mm) = a}  BY <6>kself
            <7> QED BY <7>1, <6>tceq
          <6>yinM. y \in {yy \in (Messages \ Proposals) : Sig(yy) = a /\ TranExclusive(yy) = T}
            BY <6>Teq
          <6>Mnonempty. \E yy \in (Messages \ Proposals) : Sig(yy) = a /\ TranExclusive(yy) = T
            BY <6>yinM
          <6>wpick. PICK ysent \in {yy \in (Messages \ Proposals) :
                                      Sig(yy) = a /\ TranExclusive(yy) = T} :
                      Msgs' = Msgs \cup {ysent}
            BY <4>eff, <4>selfcase, <6>Mnonempty
          <6>ycex. \E yc \in (Messages \ Proposals) :
                     /\ Sig(yc) = a
                     /\ TranExclusive(yc) = TranClosure(known \cup {p})
                     /\ yc \in Msgs'
            BY <6>wpick, <6>Teq
          <6> PICK yc \in (Messages \ Proposals) :
                /\ Sig(yc) = a
                /\ TranExclusive(yc) = TranClosure(known \cup {p})
                /\ yc \in Msgs'
            BY <6>ycex
          <6>dphyp. DPFreshHypR(alpha, bal, m, p, a, known, yc, CaughtS({ww \in am : B(ww) < B(p)}))
            <7>1. alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  OBVIOUS
            <7>2. \A x \in TranClosure(m) : B(x) <= bal  OBVIOUS
            <7>3. DecideableProposalTranExclusive(m) \subseteq Tran(p)  OBVIOUS
            <7>4. B(p) > bal  OBVIOUS
            <7>5. Sig(p) \notin Acceptors  OBVIOUS
            <7>6. V(p) = DecideableProposalV(alpha, bal, m)  OBVIOUS
            <7>7. \A w \in TranClosure(known \cup {p}) :
                    (w # p) => (\/ ((B(w) <= bal) /\ (w \in TranClosure(m)))
                                \/ ((B(w) > bal) /\ (B(w) < B(p)) /\ (V(w) = V(p))))
              BY <6>tcl
            <7>8. CaughtS(TranClosure(known \cup {p})) \subseteq CaughtS({ww \in am : B(ww) < B(p)})
              BY <6>cs2
            <7>9. ConFromCaught(alpha, CaughtS({ww \in am : B(ww) < B(p)}))
                    = ConFromCaught(alpha, CaughtS(TranClosure(m)))
              OBVIOUS
            <7>10. Sig(yc) = a  OBVIOUS
            <7>11. TranExclusive(yc) = TranClosure(known \cup {p})  OBVIOUS
            <7>12. a \notin CaughtS(TranClosure(known \cup {p}))  OBVIOUS
            <7> QED BY <7>1, <7>2, <7>3, <7>4, <7>5, <7>6, <7>7, <7>8, <7>9, <7>10, <7>11, <7>12
              DEF DPFreshHypR
          <6>fr. /\ B(yc) = B(p)
                 /\ IsOneB(yc)
                 /\ Fresh(alpha, yc)
            BY <1>aacc, <6>knownmsgs, <6>dphyp, DecideableProposalOneBFreshRW
          <6>ycmsg. yc \in Messages  OBVIOUS
          <6>freshdef. Fresh(alpha, yc) = CombinedFreshQdLrnsId(yc).fresh[alpha]
            BY <1>mi, <6>ycmsg, FreshDef
          <6>hd. HasDepth(alpha, yc, 0)  BY <6>fr, <1>aacc, <6>freshdef DEF HasDepth
          <6> QED BY <6>fr, <6>hd
        <5> QED BY <5>oldcase, <5>newcase
      <4>othercase. CASE ~(self1 = a /\ self2 = p)
        <5>kold. p \in known_messages[a]
          <6>c1. CASE self1 = a
            <7>1. known_messages'[a] = known_messages[a] \cup {self2}
              BY <6>c1, <4>eff, <2>i, <1>a
            <7>2. self2 # p  BY <4>othercase, <6>c1
            <7>3. p \in known_messages[a] \cup {self2}  BY <2>case, <7>1
            <7> QED BY <7>2, <7>3
          <6>c2. CASE self1 # a
            <7>1. known_messages'[a] = known_messages[a]
              BY <6>c2, <4>eff, <2>i, <1>a, <4>self1a
            <7> QED BY <2>case, <7>1
          <6> QED BY <6>c1, <6>c2
        <5>q. Q  BY <5>kold
        <5>net. Msgs \subseteq Msgs'  BY <4>eff
        <5> QED BY <5>q, <5>net
      <4> QED BY <4>selfcase, <4>othercase
    <3>byzcase. CASE \E self \in ByzSenders : byz(self)
      <4> PICK self \in ByzSenders : byz(self)  BY <3>byzcase
      <4>k. known_messages' = known_messages  BY DEF byz
      <4>keq. known_messages'[a] = known_messages[a]  BY <4>k
      <4>netmono. Msgs \subseteq Msgs'
        <5>1. PICK yy \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
                Msgs' = (Msgs \cup {yy})  BY <3>byzcase DEF byz
        <5> QED BY <5>1
      <4>pk. p \in known_messages[a]  BY <2>case, <4>keq
      <4>q. Q  BY <4>pk
      <4> QED BY <4>q, <4>netmono
    <3>stutcase. CASE UNCHANGED vars
      <4>k. known_messages' = known_messages /\ Msgs' = Msgs  BY <3>stutcase DEF vars
      <4>keq. known_messages'[a] = known_messages[a]  BY <4>k
      <4>pk. p \in known_messages[a]  BY <2>case, <4>keq
      <4>q. Q  BY <4>pk
      <4> QED BY <4>q, <4>k
    <3> QED BY <3>nextcase, <3>byzcase, <3>stutcase DEF Next
  <2>notcase. CASE p \notin known_messages'[a]  BY <2>notcase
  <2> QED BY <2>case, <2>notcase
<1>ji. Init => DZJoint(alpha, p, a)
  <2> SUFFICES ASSUME Init PROVE DZJoint(alpha, p, a)  BY DEF DZJoint
  <2> QED  BY <1>initt, InitInv, InitKnownClosureT, InitSelfSentT,
              InitSelfSentNotProposalT, InitChain DEF DZJoint
<1>js. DZJoint(alpha, p, a) /\ [Next]_vars => (DZJoint(alpha, p, a))'
  <2> SUFFICES ASSUME DZJoint(alpha, p, a), [Next]_vars PROVE (DZJoint(alpha, p, a))'
    BY DEF DZJoint
  <2> USE DEF DZJoint
  <2>sui. SafeAcceptorsUncaughtInvariant  BY ChainImpliesUncaught
  <2>dz. (DZInvT(alpha, p, a))'  BY <1>step, <2>sui
  <2>iv. Inv'  BY InvStep
  <2>kn. KnownTranClosureInvT'  BY InvStep, KnownClosureStepT
  <2>ss. SelfSentBoundedInvT'  BY InvStep, SelfSentStepT
  <2>sn. SelfSentNotProposalInvT'  BY InvStep, SelfSentNotProposalStepT
  <2>ch. SafeAcceptorChainInv'  BY InvStep, ChainStep
  <2> QED  BY <2>dz, <2>iv, <2>kn, <2>ss, <2>sn, <2>ch
<1>jbox. Spec => []DZJoint(alpha, p, a)  BY <1>ji, <1>js, PTL DEF Spec
<1> QED BY <1>jbox, PTL DEF DZJoint, DZInvT
====================================================================
