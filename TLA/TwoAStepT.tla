------------------------------ MODULE TwoAStepT ------------------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        InvStep, ChainStep, CaughtSMonoT, TwoAConstructT,
        BAchievedByProposal, LeFromEqT, LeTransBallotsT, EqFromLeGeBallotsT,
        MaxBSetProperty, BBallot, QuorumUpward, HasDepthDef, HasDepthDownward

LEMMA TwoAStepT ==
  MessageInterfaceAssumptions /\ LearnerGraphAssumptions /\ AcceptorsAssumptions /\
  Inv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ SelfSentNotProposalInvT /\
  SafeAcceptorChainInv /\ TwoAInvariantT /\ [Next]_vars => TwoAInvariantT'
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
                    Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
                    SafeAcceptorChainInv, TwoAInvariantT, [Next]_vars
             PROVE TwoAInvariantT'  OBVIOUS
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
  BY DEF Inv
<1>2. CASE vars' = vars
  BY <1>2, TwoAInvariantT DEF TwoAInvariantT, vars
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
  <2>xmsg. x \in Messages  BY <2>2, <1>i
  <2>xte. TranExclusive(x) \subseteq known_messages[self]  BY <2>2
  <2> DEFINE T == (known_messages'[self] \cup {x}) \cup {m \in Msgs : Sig(m) = self}
  <2> DEFINE TU == (known_messages[self] \cup {x}) \cup {m \in Msgs : Sig(m) = self}
  <2>tueqt. TU = T  BY <2>kself
  <2>net. Msgs' = (IF \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
                        THEN Msgs \cup {CHOOSE y \in (Messages \ Proposals) :
                                            Sig(y) = self /\ TranExclusive(y) = T}
                        ELSE Msgs)
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
  <2>tsub. TU \subseteq Msgs'
    <3>1. known_messages'[self] \subseteq Msgs'  BY <2>invp DEF Inv
    <3>2. {m \in Msgs : Sig(m) = self} \subseteq Msgs  OBVIOUS
    <3>3. x \in known_messages'[self]  BY <2>kself
    <3>4. known_messages[self] \subseteq known_messages'[self]  BY <2>kself
    <3>5. known_messages[self] \subseteq Msgs'  BY <3>4, <3>1
    <3> QED BY <3>1, <3>2, <3>3, <3>5, <2>netmono
  <2>tcnet. TranClosure(TU) \subseteq Msgs'
    <3> SUFFICES ASSUME NEW z \in TranClosure(TU) PROVE z \in Msgs'  OBVIOUS
    <3>1. PICK w \in TU : z \in Tran(w)  BY DEF TranClosure
    <3>2. w \in Msgs'  BY <3>1, <2>tsub
    <3>3. z = w \/ z \in TranExclusive(w)  BY <3>1 DEF Tran, TranExclusive
    <3>4. TranExclusive(w) \subseteq Msgs'  BY <3>2, <2>invp DEF Inv
    <3> QED BY <3>2, <3>3, <3>4
  <2>tuncaughtU. self \notin CaughtS(TranClosure(TU))  BY <2>tcnet, <2>uncp2, CaughtSMonoT
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW alpha \in Learners,
                      NEW d \in (1..MaxDepth(alpha)),
                      \A xx \in known_messages'[s] : (IsProposal(xx) => B(xx) <= b),
                      SigS({xx \in known_messages'[s] :
                            B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
               PROVE \E twoa \in Msgs' :
                       B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
    BY DEF TwoAInvariantT
  <2>scase. CASE s # self
    <3>keq. known_messages'[s] = known_messages[s]  BY <2>2, <2>scase, <1>i, <2>1a
    <3>bound. \A xx \in known_messages[s] : (IsProposal(xx) => B(xx) <= b)  BY <3>keq
    <3>quo. SigS({xx \in known_messages[s] : B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
      BY <3>keq
    <3>old. \E twoa \in Msgs : B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
      BY <3>bound, <3>quo, TwoAInvariantT DEF TwoAInvariantT
    <3> PICK twoa \in Msgs : B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
      BY <3>old
    <3> QED BY <2>netmono
  <2>sceq. CASE s = self
    <3>bound2. \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b
      <4> SUFFICES ASSUME NEW ww \in known_messages[self], IsProposal(ww) PROVE B(ww) <= b  OBVIOUS
      <4>1. ww \in known_messages'[self]  BY <2>kself
      <4>2. ww \in known_messages'[s]  BY <4>1, <2>sceq
      <4> QED BY <4>2
    <3>contribcase. CASE B(x) = b /\ HasDepth(alpha, x, d-1)
      <4>quoKPpre. SigS({xx \in (known_messages[self] \cup {x}) :
                         B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
        <5>1. known_messages[self] \cup {x} = known_messages'[s]  BY <2>kself, <2>sceq
        <5> QED BY <5>1
      <4>ex. \E x2 \in Messages :
               /\ (x2 \in TU \/ TranExclusive(x2) = TU)
               /\ B(x2) = b
               /\ Sig(x2) = self
               /\ HasDepth(alpha, x2, d)
               /\ self \notin Caught(x2)
               /\ IsTwoA(x2)
        BY <2>1a, <2>xmsg, <2>xte, <3>contribcase, <4>quoKPpre, <3>bound2, <2>tuncaughtU,
           MessageInterfaceAssumptions, LearnerGraphAssumptions, TwoAConstructT
      <4> PICK x2 \in Messages :
            /\ (x2 \in TU \/ TranExclusive(x2) = TU)
            /\ B(x2) = b
            /\ Sig(x2) = self
            /\ HasDepth(alpha, x2, d)
            /\ self \notin Caught(x2)
            /\ IsTwoA(x2)
        BY <4>ex
      <4>case1. CASE x2 \in TU
        <5>x2net. x2 \in Msgs'  BY <4>case1, <2>tsub
        <5> QED BY <5>x2net, <2>sceq
      <4>case2. CASE TranExclusive(x2) = TU
        <5>tex2t. TranExclusive(x2) = T  BY <4>case2, <2>tueqt
        <5>x2notprop. x2 \notin Proposals  BY DEF IsTwoA, IsProposal
        <5>ifcond. \E y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
          BY <5>tex2t, <5>x2notprop
        <5> DEFINE y0 == CHOOSE y \in (Messages \ Proposals) : Sig(y) = self /\ TranExclusive(y) = T
        <5>y0props. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = T
          BY <5>ifcond
        <5>y0propsU. y0 \in (Messages \ Proposals) /\ Sig(y0) = self /\ TranExclusive(y0) = TU
          BY <5>y0props, <2>tueqt
        <5>y0net. Msgs' = Msgs \cup {y0}  BY <2>net, <5>ifcond
        <5>y0in. y0 \in Msgs'  BY <5>y0net
        \* Inlined (rather than cited) copy of TwoAAnyWitnessT's proof, substituting
        \* y0 for y and TU for its internal T: repeated attempts to cite
        \* TwoAAnyWitnessT directly from this deeply-nested nine-hypothesis call
        \* site failed for the backend regardless of how the hypotheses were
        \* packaged, so we fall back to the reliable inlined form.
        <5>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal /\ TranTrans /\ TranAcyclic
          BY DEF MessageInterfaceAssumptions
        <5>KPT. TranExclusive(y0) = TU  BY <5>y0propsU
        <5>ynotprop. y0 \notin Proposals  BY <5>y0propsU
        <5>y0msg. y0 \in Messages  BY <5>y0propsU
        <5>y0sig. Sig(y0) = self  BY <5>y0propsU
        <5>tbound2. \A w \in TU : B(w) <= b
          <6> SUFFICES ASSUME NEW w \in TU PROVE B(w) <= b  OBVIOUS
          <6>wm. w \in Messages  BY <2>xte, <2>xmsg, <1>i
          <6>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <6>wm, BAchievedByProposal
          <6> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <6>ach
          <6>kpcase. CASE w \in (known_messages[self] \cup {x})
            <7>qw. q = w \/ q \in TranExclusive(w)  BY DEF Tran, TranExclusive
            <7>xcase. CASE w = x
              <8>1. B(w) = B(x)  BY <7>xcase
              <8>2. B(x) = b  BY <3>contribcase
              <8>3. B(w) = b  BY <8>1, <8>2
              <8>4. b \in Ballots  OBVIOUS
              <8>5. B(w) \in Ballots  BY <8>3, <8>4
              <8> QED BY <8>3, <8>4, <8>5, LeFromEqT
            <7>kcase. CASE w \in known_messages[self]
              <8>1. q = w \/ q \in known_messages[self]
                <9>1. TranExclusive(w) \subseteq known_messages[self]
                  <10>a. Tran(w) \subseteq TranClosure(known_messages[self])  BY <7>kcase DEF TranClosure
                  <10>b. TranClosure(known_messages[self]) = known_messages[self]
                    BY KnownTranClosureInvT DEF KnownTranClosureInvT
                  <10>c. TranExclusive(w) \subseteq Tran(w)  BY DEF Tran, TranExclusive
                  <10> QED BY <10>a, <10>b, <10>c
                <9> QED BY <7>qw, <9>1
              <8>2. q \in known_messages[self]  BY <8>1, <7>kcase
              <8>3. IsProposal(q)  OBVIOUS
              <8>4. B(q) <= b  BY <8>2, <8>3, <3>bound2
              <8>5. B(q) = B(w)  OBVIOUS
              <8> QED BY <8>4, <8>5
            <7> QED BY <7>xcase, <7>kcase, <6>kpcase
          <6>sscase. CASE w \in {mm \in Msgs : Sig(mm) = self}
            <7>notprop. ~IsProposal(w)
              <8>1. w \in Msgs /\ Sig(w) = self  BY <6>sscase
              <8> QED BY <8>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
            <7>qnw. q # w  BY <7>notprop
            <7>qte. q \in TranExclusive(w)  BY <7>qnw DEF Tran, TranExclusive
            <7>bound2. TranExclusive(w) \subseteq known_messages[self] \cup {mm \in Msgs : Sig(mm) = self}
              BY <6>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
            <7>qkorself. q \in known_messages[self] \/ q \in {mm \in Msgs : Sig(mm) = self}
              BY <7>qte, <7>bound2
            <7>qisprop. IsProposal(q)  OBVIOUS
            <7>notselfprop. q \notin {mm \in Msgs : Sig(mm) = self}
              <8> SUFFICES ASSUME q \in {mm \in Msgs : Sig(mm) = self} PROVE FALSE  OBVIOUS
              <8>1. q \in Msgs /\ Sig(q) = self  OBVIOUS
              <8> QED BY <8>1, <7>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
            <7>qk. q \in known_messages[self]  BY <7>qkorself, <7>notselfprop
            <7>qbound. B(q) <= b  BY <7>qk, <7>qisprop, <3>bound2
            <7>qbw. B(q) = B(w)  OBVIOUS
            <7> QED BY <7>qbound, <7>qbw
          <6> QED BY <6>kpcase, <6>sscase
        <5>xachieve. \E q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = b /\ B(q) = b
          <6>ach. \E q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = B(x) /\ B(q) = B(x)
            BY BAchievedByProposal
          <6> QED BY <6>ach, <3>contribcase
        <5> PICK qx \in Tran(x) : IsProposal(qx) /\ ProposalBal(qx) = b /\ B(qx) = b  BY <5>xachieve
        <5>qxTU. qx \in TU
          <6>1. Tran(x) \subseteq (known_messages[self] \cup {x})
            <7>a. x \in (known_messages[self] \cup {x})  OBVIOUS
            <7>b. TranExclusive(x) \subseteq (known_messages[self] \cup {x})  BY <2>xte
            <7>c. Tran(x) = {x} \cup TranExclusive(x)  BY DEF Tran, TranExclusive
            <7> QED BY <7>a, <7>b, <7>c
          <6> QED BY <6>1
        <5>ybal. B(y0) = b
          <6> DEFINE Cand == Proposals \cap Tran(y0)
          <6>tranY. Tran(y0) = {y0} \cup TU  BY <5>KPT DEF Tran, TranExclusive
          <6>candeq. Cand = Proposals \cap TU
            <7>1. y0 \notin Proposals  BY <5>ynotprop
            <7> QED BY <6>tranY, <7>1
          <6>qxincand. qx \in Cand
            <7>a. qx \in Proposals  BY DEF IsProposal
            <7> QED BY <6>candeq, <7>a, <5>qxTU
          <6>ubound. \A z \in Cand : ProposalBal(z) <= b
            <7> SUFFICES ASSUME NEW z \in Cand PROVE ProposalBal(z) <= b  OBVIOUS
            <7>1. z \in TU  BY <6>candeq
            <7>2. IsProposal(z)  BY <6>candeq DEF IsProposal
            <7>3. z \in Messages  BY <7>1, <2>xte, <2>xmsg, <1>i
            <7>4. z \in GetProposals(z)
              <8>1. z \in Tran(z)  BY DEF Tran
              <8> QED BY <8>1, <6>candeq DEF GetProposals
            <7>5. ProposalBal(z) <= B(z)
              <8>fin. IsFiniteSet(GetProposals(z))
                <9>1. GetProposals(z) \subseteq Tran(z)  BY DEF GetProposals
                <9>2. IsFiniteSet(Tran(z))  BY <7>3, <5>mi DEF TranFinite
                <9> QED BY <9>1, <9>2, FS_Subset
              <8>sub. GetProposals(z) \subseteq Proposals  BY DEF GetProposals
              <8>ne. GetProposals(z) # {}  BY <7>4
              <8>choose. /\ B(z) \in {ProposalBal(w) : w \in GetProposals(z)}
                         /\ \A ww \in {ProposalBal(w) : w \in GetProposals(z)} : B(z) >= ww
                BY <8>fin, <8>sub, <8>ne, <5>mi, MaxBSetProperty DEF B
              <8>mem. ProposalBal(z) \in {ProposalBal(w) : w \in GetProposals(z)}  BY <7>4
              <8> QED BY <8>choose, <8>mem
            <7>6. B(z) <= b  BY <7>1, <5>tbound2
            <7>7. ProposalBal(z) \in Ballots
              <8>1. MessageInterface.proposalbal \in [Proposals -> Ballots]
                BY <5>mi DEF TypeOKMessageInterface
              <8>2. z \in Proposals  BY <7>2 DEF IsProposal
              <8> QED BY <8>1, <8>2 DEF ProposalBal
            <7>8. B(z) \in Ballots  BY <5>mi, <7>3, BBallot
            <7>9. b \in Ballots  OBVIOUS
            <7> QED BY <7>5, <7>6, <7>7, <7>8, <7>9, LeTransBallotsT
          <6>candfin. IsFiniteSet(Cand)
            <7>ysub. Cand \subseteq Tran(y0)  OBVIOUS
            <7>yfin. IsFiniteSet(Tran(y0))  BY <5>mi, <5>y0msg DEF TranFinite
            <7> QED BY <7>ysub, <7>yfin, FS_Subset
          <6>candsub. Cand \subseteq Proposals  OBVIOUS
          <6>candne. Cand # {}  BY <6>qxincand
          <6>ychoose. /\ B(y0) \in {ProposalBal(w) : w \in Cand}
                      /\ \A ww \in {ProposalBal(w) : w \in Cand} : B(y0) >= ww
            BY <6>candfin, <6>candsub, <6>candne, <5>mi, MaxBSetProperty DEF B, GetProposals
          <6>yge. B(y0) >= b
            <7>1. ProposalBal(qx) \in {ProposalBal(w) : w \in Cand}  BY <6>qxincand
            <7> QED BY <7>1, <6>ychoose
          <6>yle. B(y0) <= b
            <7>pw. PICK w \in Cand : B(y0) = ProposalBal(w)  BY <6>ychoose
            <7> QED BY <7>pw, <6>ubound
          <6>yty. y0 \in Messages  BY <5>y0propsU
          <6>ybalty. B(y0) \in Ballots  BY <5>mi, <6>yty, BBallot
          <6>bty. b \in Ballots  OBVIOUS
          <6> QED BY <6>yge, <6>yle, <6>ybalty, <6>bty, EqFromLeGeBallotsT
        <5>qdeq. {q \in TranExclusive(y0) : B(y0) = B(q) /\ HasDepth(alpha, q, d-1)}
                   = {xx \in TU : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
          BY <5>KPT, <5>ybal
        <5>dpos. d >= 1  OBVIOUS
        <5>qdval. Qd(alpha, y0, d) = {xx \in TU : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
          BY <5>dpos, <5>qdeq DEF Qd
        <5>subKPT. {xx \in (known_messages[self] \cup {x}) : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
                     \subseteq {xx \in TU : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
          OBVIOUS
        <5>sigsub. SigS({xx \in (known_messages[self] \cup {x}) : B(xx) = b /\ HasDepth(alpha, xx, d-1)})
                     \subseteq SigS(Qd(alpha, y0, d))
          BY <5>subKPT, <5>qdval DEF SigS
        <5>qdfin. IsFiniteSet(Qd(alpha, y0, d))
          <6>1. Qd(alpha, y0, d) \subseteq TU  BY <5>qdval
          <6>2. IsFiniteSet(TU)
            <7>0. known_messages[self] \subseteq Msgs  BY <1>i
            <7>0b. IsFiniteSet(known_messages[self])  BY <7>0, <1>i, FS_Subset
            <7>1. IsFiniteSet(known_messages[self] \cup {x})  BY <7>0b, FS_AddElement
            <7>2. IsFiniteSet({mm \in Msgs : Sig(mm) = self})  BY <1>i, FS_Subset
            <7> QED BY <7>1, <7>2, FS_Union
          <6> QED BY <6>1, <6>2, FS_Subset
        <5>sigfin. IsFiniteSet(SigS(Qd(alpha, y0, d)))  BY <5>qdfin, FS_Image DEF SigS
        <5>sigacc. SigS(Qd(alpha, y0, d)) \subseteq Acceptors
          <6> SUFFICES ASSUME NEW aa \in SigS(Qd(alpha, y0, d)) PROVE aa \in Acceptors  OBVIOUS
          <6>1. PICK q \in Qd(alpha, y0, d) : aa = Sig(q)  BY DEF SigS
          <6>2. HasDepth(alpha, q, d-1)  BY <6>1, <5>qdval
          <6>3. Sig(q) \in Acceptors  BY <6>2 DEF HasDepth
          <6> QED BY <6>1, <6>3
        <5>quo. SigS(Qd(alpha, y0, d)) \in Quorums(alpha)
          BY <5>sigsub, <5>sigfin, <5>sigacc, <4>quoKPpre, QuorumUpward
        <5>hd. HasDepth(alpha, y0, d)
          <6>ysig. Sig(y0) \in Acceptors  BY <2>1a, <5>y0sig DEF AcceptorsAssumptions, SafeAcceptorsAssumption
          <6>hddef. HasDepth(alpha, y0, d) =
                      (/\ Sig(y0) \in Acceptors
                       /\ IF d = 0 THEN (IsOneB(y0) /\ Fresh(alpha, y0))
                                   ELSE SigS(Qd(alpha, y0, d)) \in Quorums(alpha))
            BY <5>mi, <5>y0msg, HasDepthDef
          <6>dne0. d # 0  BY <5>dpos
          <6> QED BY <6>ysig, <6>hddef, <6>dne0, <5>quo
        <5>hd1. HasDepth(alpha, y0, 1)
          <6>lga. LearnersMightAgree /\ ValidLearnerGraphAssumption  BY DEF LearnerGraphAssumptions
          <6> QED BY <5>mi, <5>y0msg, <6>lga, <5>hd, <5>dpos, HasDepthDownward
        <5>istwoa. IsTwoA(y0)
          <6>1. ~IsProposal(y0)  BY <5>ynotprop DEF IsProposal
          <6> QED BY <6>1, <5>hd1 DEF IsTwoA
        <5>y0any. B(y0) = b /\ HasDepth(alpha, y0, d) /\ IsTwoA(y0)
          BY <5>ybal, <5>hd, <5>istwoa
        <5> QED BY <5>y0in, <5>y0props, <5>y0any, <2>sceq
      <4> QED BY <4>case1, <4>case2
    <3>notcontribcase. CASE ~(B(x) = b /\ HasDepth(alpha, x, d-1))
      <4>seteq. {xx \in known_messages[self] : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
                  = {xx \in (known_messages[self] \cup {x}) : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
        BY <3>notcontribcase
      <4>quopre. SigS({xx \in known_messages[self] : B(xx) = b /\ HasDepth(alpha, xx, d-1)})
                   \in Quorums(alpha)
        <5>1. known_messages[self] \cup {x} = known_messages'[s]  BY <2>kself, <2>sceq
        <5>2. SigS({xx \in (known_messages[self] \cup {x}) :
                    B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
          BY <5>1
        <5> QED BY <4>seteq, <5>2
      <4>old. \E twoa \in Msgs : B(twoa) = b /\ Sig(twoa) = self /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
        BY <3>bound2, <4>quopre, TwoAInvariantT DEF TwoAInvariantT
      <4> PICK twoa \in Msgs :
            B(twoa) = b /\ Sig(twoa) = self /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)  BY <4>old
      <4> QED BY <2>netmono, <2>sceq
    <3> QED BY <3>contribcase, <3>notcontribcase
  <2> QED BY <2>scase, <2>sceq
<1>4. CASE \E self \in ByzSenders : byz(self)
  <2>1. PICK self \in ByzSenders : byz(self)  BY <1>4
  <2>2. PICK y \in {z \in Messages : Sig(z) = self /\ TranExclusive(z) \subseteq Msgs} :
              Msgs' = (Msgs \cup {y})
     BY <2>1 DEF byz
  <2>k. known_messages' = known_messages  BY <2>1 DEF byz
  <2>netmono. Msgs \subseteq Msgs'  BY <2>2
  <2> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW b \in Ballots, NEW alpha \in Learners,
                      NEW d \in (1..MaxDepth(alpha)),
                      \A xx \in known_messages'[s] : (IsProposal(xx) => B(xx) <= b),
                      SigS({xx \in known_messages'[s] :
                            B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
               PROVE \E twoa \in Msgs' :
                       B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
    BY DEF TwoAInvariantT
  <2>keq. known_messages'[s] = known_messages[s]  BY <2>k
  <2>bound. \A xx \in known_messages[s] : (IsProposal(xx) => B(xx) <= b)  BY <2>keq
  <2>quo. SigS({xx \in known_messages[s] : B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
    BY <2>keq
  <2>old. \E twoa \in Msgs : B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
    BY <2>bound, <2>quo, TwoAInvariantT DEF TwoAInvariantT
  <2> PICK twoa \in Msgs : B(twoa) = b /\ Sig(twoa) = s /\ HasDepth(alpha, twoa, d) /\ IsTwoA(twoa)
    BY <2>old
  <2> QED BY <2>netmono
<1> QED BY <1>2, <1>3, <1>4 DEF Next
====================================================================
