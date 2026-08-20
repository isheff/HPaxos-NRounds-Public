------------------------- MODULE SelfKnownClassifiedR -------------------------
EXTENDS HPaxosPlusCal, BBallot, BAchievedByProposal

\* Relaxed analogue of SelfKnownBoundedByUniqueT: everything self knows or has
\* sent is either low (<= bal) or a V(p)-valued message strictly below B(p).
LEMMA SelfKnownClassifiedR ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, self \in LiveAcceptors,
         NEW p \in Proposals, NEW bal \in Ballots,
         B(p) > bal,
         p \notin known_messages[self],
         \A z \in Proposals : ((z \in RelevantMsgs) /\ (B(z) > bal)) =>
           ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p))),
         NEW w \in (known_messages[self] \cup {mm \in Msgs : Sig(mm) = self})
  PROVE (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p)))
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
  BY DEF Inv
<1>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1> DEFINE Rel(z) == ((z \in RelevantMsgs) /\ (B(z) > bal)) =>
                       ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))
<1>relhyp. \A z \in Proposals : Rel(z)  BY DEF Rel
<1> HIDE DEF Rel
<1>wor. w \in known_messages[self] \/ w \in {mm \in Msgs : Sig(mm) = self}  OBVIOUS
<1>wmsg. w \in Messages  BY <1>wor, <1>i
<1>wnet. w \in Msgs  BY <1>wor, <1>i
<1>wte. TranExclusive(w) \subseteq known_messages[self] \cup {mm \in Msgs : Sig(mm) = self}
  <2>1. CASE w \in known_messages[self]
    <3>a. Tran(w) \subseteq TranClosure(known_messages[self])  BY <2>1 DEF TranClosure
    <3>b. TranClosure(known_messages[self]) = known_messages[self]
      BY KnownTranClosureInvT DEF KnownTranClosureInvT
    <3>c. TranExclusive(w) \subseteq Tran(w)  BY DEF Tran, TranExclusive
    <3> QED BY <3>a, <3>b, <3>c
  <2>2. CASE w \in {mm \in Msgs : Sig(mm) = self}
    BY <2>2, SelfSentBoundedInvT DEF SelfSentBoundedInvT
  <2> QED BY <1>wor, <2>1, <2>2
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bwnat. B(w) \in Ballots  BY <1>wmsg, <1>mi, BBallot
<1>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>bpnat. B(p) \in Ballots  BY <1>pmsg, <1>mi, BBallot
<1>case. B(w) <= bal \/ B(w) > bal  BY <1>bwnat, <1>balnat DEF Ballots
<1>casehigh. CASE B(w) > bal
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <1>wmsg, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>ach
  <2>qprop. q \in Proposals  BY DEF IsProposal
  <2>qmsg. q \in Messages  BY <2>qprop, <1>mi DEF TypeOKMessageInterface
  <2>bqnat. B(q) \in Ballots  BY <2>qmsg, <1>mi, BBallot
  <2>qbalpos. B(q) > bal  BY <1>casehigh
  <2>qcase. q = w \/ q \in TranExclusive(w)  BY DEF Tran, TranExclusive
  <2>qnet. q \in Msgs
    <3>1. CASE q = w  BY <3>1, <1>wnet
    <3>2. CASE q \in TranExclusive(w)  BY <3>2, <1>wte, <1>i
    <3> QED BY <2>qcase, <3>1, <3>2
  <2>qin. q \in known_messages[self] \cup {mm \in Msgs : Sig(mm) = self}
    BY <2>qcase, <1>wor, <1>wte
  <2>qrel. q \in RelevantMsgs
    BY <2>qin, <2>qnet DEF RelevantMsgs, LiveRelevant
  <2>relq. Rel(q)  BY <2>qprop, <1>relhyp
  <2>qconc. (V(q) = V(p)) /\ ((B(q) < B(p)) \/ (q = p))
    BY <2>relq, <2>qrel, <2>qbalpos DEF Rel
  <2>notself. p \notin {mm \in Msgs : Sig(mm) = self}
    <3>allns. \A mm \in Msgs : Sig(mm) = self => ~IsProposal(mm)
      BY SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3> QED BY <3>allns DEF IsProposal
  <2>qnotp. q # p
    <3> SUFFICES ASSUME q = p PROVE FALSE  OBVIOUS
    <3>c1. CASE q = w
      <4>1. w = p  BY <3>c1
      <4>2. p \in known_messages[self] \/ p \in {mm \in Msgs : Sig(mm) = self}
        BY <4>1, <1>wor
      <4> QED BY <4>2, <2>notself
    <3>c2. CASE q \in TranExclusive(w)
      <4>pinw. p \in TranExclusive(w)  BY <3>c2
      <4>pk. p \in known_messages[self] \/ p \in {mm \in Msgs : Sig(mm) = self}
        BY <4>pinw, <1>wte
      <4> QED BY <4>pk, <2>notself
    <3> QED BY <2>qcase, <3>c1, <3>c2
  <2>qlt. B(q) < B(p)  BY <2>qconc, <2>qnotp
  <2>beq. B(w) = B(q)  OBVIOUS
  <2>bwlt. B(w) < B(p)  BY <2>qlt, <2>beq, <1>bwnat, <2>bqnat, <1>bpnat DEF Ballots
  <2>vwq. V(w) = V(q)  BY <2>beq DEF V
  <2>vw. V(w) = V(p)  BY <2>vwq, <2>qconc
  <2> QED BY <2>bwlt, <2>vw
<1>caselow. CASE B(w) <= bal  BY <1>caselow
<1> QED BY <1>case, <1>casehigh, <1>caselow
====================================================================
