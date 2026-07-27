------------------------------ MODULE Termination ------------------------------
EXTENDS HPaxosPlusCal, BBallot,
        IsAllMessagesEverSentExists, TemporalDecideableProposalExists,
        TerminatingProposal

THEOREM Termination ==
  \A alpha \in Learners : \* we'll show we can make alpha decide
    \* but we have to know stuff about all messages with ballot <= bal,
    \*  and then make the only proposal with ballot > bal
  \A bal \in Ballots :
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ AcceptorsAssumptions
   /\ NetworkAssumption
   /\ LiveAcceptors \in Quorums(alpha) \* alpha has a live quorum
   /\ SafeAcceptors \in SafetySets({alpha}) \* alpha must agree with itself
  ) =>
  \* there is some "correct" proposal p such that
  \E p \in Proposals :
  (( \* If p is the only proposal with ballot > bal that will ever be sent
   /\ \A x \in Proposals : (((<>(x \in Msgs)) /\ (B(x) > bal)) => (x = p))
     \* and p is eventually sent
   /\ <>(p \in Msgs)
  ) =>
  \* alpha eventually decides
  <> Decision(Msgs, alpha, B(p)))
<1> SUFFICES ASSUME NEW alpha \in Learners, NEW bal \in Ballots,
                    Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions,
                    LearnerGraphAssumptions, AcceptorsAssumptions, NetworkAssumption,
                    LiveAcceptors \in Quorums(alpha),
                    SafeAcceptors \in SafetySets({alpha})
             PROVE  \E p \in Proposals :
                    (( /\ \A x \in Proposals : (((<>(x \in Msgs)) /\ (B(x) > bal)) => (x = p))
                       /\ <>(p \in Msgs)
                    ) => <> Decision(Msgs, alpha, B(p)))
  OBVIOUS
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal /\ TranAcyclic
  BY DEF MessageInterfaceAssumptions
\* allmessages = the ever-sent set; M = {m \in allmessages : B(m)<=bal} is the
\* ever-sent, ballot-<=-bal set (no <> inside the set-builder -- SANY-clean).
<1> PICK allmessages : IsAllMessagesEverSent(allmessages)  BY IsAllMessagesEverSentExists
<1>amsub. allmessages \subseteq Messages
  <2> SUFFICES ASSUME NEW mm \in allmessages PROVE mm \in Messages  OBVIOUS
  <2>1. mm \in allmessages <=> IAMESCond(mm)  BY DEF IsAllMessagesEverSent
  <2> QED  BY <2>1 DEF IAMESCond
<1> DEFINE M == {m \in allmessages : B(m) <= bal}
\* the decideable proposal p for the ever-sent <= bal messages
<1>tdpe. \E p \in Proposals :
           (/\ TranExclusive(p) = DecideableProposalTranExclusive(M)
            /\ V(p) = DecideableProposalV(alpha, bal, M)
            /\ B(p) > bal
            /\ Sig(p) \notin Acceptors)
  BY TemporalDecideableProposalExists
<1> PICK p \in Proposals :
      /\ TranExclusive(p) = DecideableProposalTranExclusive(M)
      /\ V(p) = DecideableProposalV(alpha, bal, M)
      /\ B(p) > bal
      /\ Sig(p) \notin Acceptors
  BY <1>tdpe
<1>ppmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1> WITNESS p \in Proposals
<1> SUFFICES ASSUME \A x \in Proposals : (((<>(x \in Msgs)) /\ (B(x) > bal)) => (x = p)),
                    <>(p \in Msgs)
             PROVE  <> Decision(Msgs, alpha, B(p))
  OBVIOUS
<1>teq. TranExclusive(p) = DecideableProposalTranExclusive({m \in allmessages : B(m) <= bal})
  OBVIOUS
<1>veq. V(p) = DecideableProposalV(alpha, bal, {m \in allmessages : B(m) <= bal})
  OBVIOUS
<1>pam. p \in allmessages
  <2>pa. p \in allmessages <=> IAMESCond(p)  BY DEF IsAllMessagesEverSent
  <2> QED  BY <2>pa, <1>ppmsg DEF IAMESCond
<1>isprop. IsProposal(p)  BY DEF IsProposal
<1>bpgt. B(p) > bal  OBVIOUS
<1>signa. Sig(p) \notin Acceptors  OBVIOUS
<1>iame. IsAllMessagesEverSent(allmessages)  OBVIOUS
<1>uniqam. \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal)) => (x = p))
  <2> SUFFICES ASSUME NEW x \in allmessages, IsProposal(x), B(x) > bal PROVE x = p  OBVIOUS
  <2>xp. x \in Proposals  BY DEF IsProposal
  <2>xa. x \in allmessages <=> IAMESCond(x)  BY DEF IsAllMessagesEverSent
  <2>xnet. <>(x \in Msgs)  BY <2>xa DEF IAMESCond
  <2> QED  BY <2>xp, <2>xnet
<1> QED
  BY <1>amsub, <1>isprop, <1>signa, <1>bpgt, <1>uniqam, <1>teq, <1>veq, <1>iame, <1>pam,
     TerminatingProposal
====================================================================
