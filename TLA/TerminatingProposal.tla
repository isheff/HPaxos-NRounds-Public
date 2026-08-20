------------------------- MODULE TerminatingProposal -------------------------
EXTENDS HPaxosPlusCal,
        BBallot, TranSubMessages, BAchievedByProposal,
        BoxKnownTranClosed, TerminatingProposalRelaxed
LOCAL INSTANCE TLAPS

\* proving this will probably want to use DecideableProposalOneBExists, AlwaysOneBInvariant, AlwaysTwoAInvariant, and EventuallyKnown
THEOREM TerminatingProposal ==
  \A alpha \in Learners : \* we'll show we can make alpha decide
    \* but we have to know stuff about all messages with ballot <= bal,
    \*  and then make the only proposal with ballot > bal
  \A bal \in Ballots :
  \A allmessages : \* all messages eventually sent
  \A p \in allmessages : \* p is eventually sent
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ AcceptorsAssumptions
   /\ NetworkAssumption
   /\ LiveAcceptors \in Quorums(alpha)
   /\ SafeAcceptors \in SafetySets({alpha}) \* use SafeAcceptorsNeverCaughtInfinite to prove this means alpha \in ConFromCaught(alpha, allmessages) or whatever
   /\ IsProposal(p)
     \* To avoid "catching" anyone new, it's easiest if we just
     \*  assume p is sent by some proposer who is not an Acceptor.
   /\ Sig(p) \notin Acceptors
   /\ B(p) > bal
      \* p is the only proposal sent with ballot > bal
   /\ \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal)) => (x = p))
      \* specify p's Tran based on the set of messages sent with ballot <= bal
   /\ TranExclusive(p) = DecideableProposalTranExclusive({m \in allmessages : B(m) <= bal})
      \* specify p's value baesd on the set of messages sent with ballot <= bal
   /\ V(p) = DecideableProposalV(alpha, bal, {m \in allmessages : B(m) <= bal})
      \* the only "temporal" requirement (other than Spec and Assumptions):
      \*  allmessages is actually the set of messages that can ever be received
      \*  by SafeAcceptors.
   /\ IsAllMessagesEverKnown(allmessages)
      \* WEAKENED NetworkAssumption never forces the FIRST receipt of the
      \* Byzantine-signed proposal p (or of its history, which gates it), so
      \* fairness over Tran(p) is assumed separately.
   /\ TranFairness(p)
   \* then alpha decides on ballot B(p)
   ) => <> Decision(Msgs, alpha, B(p))
<1> SUFFICES ASSUME NEW alpha \in Learners, NEW bal \in Ballots, NEW allmessages,
                    NEW p \in allmessages, TranFairness(p),
                    Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions,
                    LearnerGraphAssumptions, AcceptorsAssumptions, NetworkAssumption,
                    LiveAcceptors \in Quorums(alpha),
                    SafeAcceptors \in SafetySets({alpha}),
                    IsProposal(p), Sig(p) \notin Acceptors, B(p) > bal,
                    \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal)) => (x = p)),
                    TranExclusive(p) = DecideableProposalTranExclusive({m \in allmessages : B(m) <= bal}),
                    V(p) = DecideableProposalV(alpha, bal, {m \in allmessages : B(m) <= bal}),
                    IsAllMessagesEverKnown(allmessages)
             PROVE  <> Decision(Msgs, alpha, B(p))
  OBVIOUS
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal /\ TranAcyclic
  BY DEF MessageInterfaceAssumptions
<1>amsub. allmessages \subseteq Messages
  <2> SUFFICES ASSUME NEW mm \in allmessages PROVE mm \in Messages  OBVIOUS
  <2>1. mm \in allmessages <=> IAMEKCond(mm)  BY DEF IsAllMessagesEverKnown
  <2> QED  BY <2>1 DEF IAMEKCond
<1>pprop. p \in Proposals  BY DEF IsProposal
<1>pmsg. p \in Messages  BY <1>pprop, <1>mi DEF TypeOKMessageInterface
<1>bpbal. B(p) \in Ballots  BY <1>pmsg, <1>mi, BBallot
<1>balnat. bal \in Nat  BY DEF Ballots
\* allmessages is closed under Tran: every ancestor of an ever-sent message is
\* itself eventually sent (BoxTranClosed + the singleton bridge, diamond-MP).
<1>amtc. \A mm \in allmessages : Tran(mm) \subseteq allmessages
  <2> SUFFICES ASSUME NEW mm \in allmessages, NEW x \in Tran(mm) PROVE x \in allmessages  OBVIOUS
  <2>mmsg. mm \in Messages  BY <1>amsub
  <2>cases. x = mm \/ x \in TranExclusive(mm)  BY DEF Tran, TranExclusive
  <2>c1. CASE x = mm  BY <2>c1
  <2>c2. CASE x \in TranExclusive(mm)
    <3>xmsg. x \in Messages  BY <2>mmsg, <1>mi, TranSubMessages
    <3>dm. <>KnownToLive(mm)
      <4>1. mm \in allmessages <=> IAMEKCond(mm)  BY DEF IsAllMessagesEverKnown
      <4> QED  BY <4>1 DEF IAMEKCond
    <3>ktcop. KTCop(mm, x)  BY <2>mmsg, <2>c2, BoxKnownTranClosed
    <3>ktc. [](KnownToLive(mm) => KnownToLive(x))  BY <3>ktcop DEF KTCop
    <3>dx. <>KnownToLive(x)  BY <3>dm, <3>ktc, PTL
    <3>1b. x \in allmessages <=> IAMEKCond(x)  BY DEF IsAllMessagesEverKnown
    <3> QED  BY <3>xmsg, <3>dx, <3>1b DEF IAMEKCond
  <2> QED  BY <2>cases, <2>c1, <2>c2
\* under uniqueness the ballot band (bal, B(p)) is EMPTY of messages, so the
\* <=bal and <B(p) prefixes of allmessages coincide:
<1>seteq. {m \in allmessages : B(m) < B(p)} = {m \in allmessages : B(m) <= bal}
  <2>sub1. {m \in allmessages : B(m) <= bal} \subseteq {m \in allmessages : B(m) < B(p)}
    <3> SUFFICES ASSUME NEW m \in allmessages, B(m) <= bal PROVE B(m) < B(p)  OBVIOUS
    <3>mmsg. m \in Messages  BY <1>amsub
    <3>bm. B(m) \in Ballots  BY <3>mmsg, <1>mi, BBallot
    <3> QED  BY <3>bm, <1>bpbal, <1>balnat DEF Ballots
  <2>sub2. {m \in allmessages : B(m) < B(p)} \subseteq {m \in allmessages : B(m) <= bal}
    <3> SUFFICES ASSUME NEW m \in allmessages, B(m) < B(p) PROVE B(m) <= bal  OBVIOUS
    <3>mmsg. m \in Messages  BY <1>amsub
    <3>bm. B(m) \in Ballots  BY <3>mmsg, <1>mi, BBallot
    <3>cases. B(m) <= bal \/ B(m) > bal  BY <3>bm, <1>balnat DEF Ballots
    <3>chigh. CASE B(m) > bal
      <4>ach. \E q \in Tran(m) : IsProposal(q) /\ B(q) = B(m)  BY <3>mmsg, BAchievedByProposal
      <4> PICK q \in Tran(m) : IsProposal(q) /\ B(q) = B(m)  BY <4>ach
      <4>qam. q \in allmessages  BY <1>amtc
      <4>qbal. B(q) > bal  BY <3>chigh
      <4>qp. q = p  BY <4>qam, <4>qbal
      <4>beq. B(m) = B(p)  BY <4>qp
      <4> QED  BY <4>beq, <3>bm, <1>bpbal DEF Ballots
    <3>clow. CASE B(m) <= bal  BY <3>clow
    <3> QED  BY <3>cases, <3>chigh, <3>clow
  <2> QED  BY <2>sub1, <2>sub2
<1>coneq. ConFromCaught(alpha, CaughtS({m \in allmessages : B(m) <= bal}))
            = ConFromCaught(alpha, CaughtS({m \in allmessages : B(m) < B(p)}))
  BY <1>seteq
<1>dpte. DecideableProposalTranExclusive({m \in allmessages : B(m) <= bal}) \subseteq Tran(p)
  <2>1. TranExclusive(p) \subseteq Tran(p)  BY DEF Tran, TranExclusive
  <2> QED  BY <2>1
<1>rel. \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal)) =>
          (/\ V(x) = DecideableProposalV(alpha, bal, {m \in allmessages : B(m) <= bal})
           /\ ((B(x) < B(p)) \/ (x = p))))
  <2> SUFFICES ASSUME NEW x \in allmessages, IsProposal(x), B(x) > bal
               PROVE /\ V(x) = DecideableProposalV(alpha, bal, {m \in allmessages : B(m) <= bal})
                     /\ ((B(x) < B(p)) \/ (x = p))
    OBVIOUS
  <2>xp. x = p  OBVIOUS
  <2>vx. V(x) = V(p)  BY <2>xp
  <2> QED  BY <2>xp, <2>vx
<1> QED
  BY <1>amsub, <1>pprop, <1>dpte, <1>rel, <1>coneq,
     TerminatingProposalRelaxed
====================================================================
