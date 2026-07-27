-------------------- MODULE TerminatingProposalRelaxed --------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        BBallot, BMonotone, TranClosureClosed, TranClosureExpanding,
        CaughtSMonoT, BoxTranClosed, NetBridge,
        SafeAcceptorsNeverCaughtInfinite, MaxDepthFiniteAcceptors,
        TerminatingProposalTwoAInductionR, LASDBDecisionW
LOCAL INSTANCE TLAPS

THEOREM TerminatingProposalRelaxed ==
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
      \* p's Tran includes a set based on the set of messages sent with ballot <= bal
   /\ DecideableProposalTranExclusive({m \in allmessages : B(m) <= bal}) \subseteq Tran(p)
      \* proposals > bal have a  value based on the set of messages sent <= bal
      \* and p has the greatest ballot
   /\ \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal )) =>
         (/\ V(x) = DecideableProposalV(alpha, bal, {m \in allmessages : B(m) <= bal})
          /\ ((B(x) < B(p)) \/ (x = p))))
      \* any new catches between ballots bal and B(p) don't change anything important.
   /\ (  ConFromCaught(alpha, CaughtS({m \in allmessages : B(m) <= bal}))
       = ConFromCaught(alpha, CaughtS({m \in allmessages : B(m) <  B(p)})))
      \* the only "temporal" requirement (other than Spec and Assumptions):
      \*  allmessages is actually the set of messages that can ever be received
      \*  by SafeAcceptors.
   /\ IsAllMessagesEverSent(allmessages)
   \* then alpha decides on ballot B(p)
   ) => <> Decision(Msgs, alpha, B(p))
<1> SUFFICES ASSUME NEW alpha \in Learners, NEW bal \in Ballots, NEW allmessages,
                    NEW p \in allmessages,
                    Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions,
                    LearnerGraphAssumptions, AcceptorsAssumptions, NetworkAssumption,
                    LiveAcceptors \in Quorums(alpha),
                    SafeAcceptors \in SafetySets({alpha}),
                    IsProposal(p), Sig(p) \notin Acceptors, B(p) > bal,
                    DecideableProposalTranExclusive({m \in allmessages : B(m) <= bal}) \subseteq Tran(p),
                    \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal)) =>
                      (/\ V(x) = DecideableProposalV(alpha, bal, {m \in allmessages : B(m) <= bal})
                       /\ ((B(x) < B(p)) \/ (x = p)))),
                    ConFromCaught(alpha, CaughtS({m \in allmessages : B(m) <= bal}))
                      = ConFromCaught(alpha, CaughtS({m \in allmessages : B(m) < B(p)})),
                    IsAllMessagesEverSent(allmessages)
             PROVE  <> Decision(Msgs, alpha, B(p))
  OBVIOUS
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal /\ TranAcyclic
  BY DEF MessageInterfaceAssumptions
<1> DEFINE M == {m \in allmessages : B(m) <= bal}
<1>amsub. allmessages \subseteq Messages
  <2> SUFFICES ASSUME NEW mm \in allmessages PROVE mm \in Messages  OBVIOUS
  <2>1. mm \in allmessages <=> IAMESCond(mm)  BY DEF IsAllMessagesEverSent
  <2> QED  BY <2>1 DEF IAMESCond
<1>msub. M \subseteq allmessages  OBVIOUS
<1>mmsg. M \in SUBSET Messages  BY <1>amsub, <1>msub
<1>pprop. p \in Proposals  BY DEF IsProposal
<1>pmsg. p \in Messages  BY <1>pprop, <1>mi DEF TypeOKMessageInterface
<1>bpbal. B(p) \in Ballots  BY <1>pmsg, <1>mi, BBallot
<1>tcsub. TranClosure(M) \subseteq allmessages
  <2> SUFFICES ASSUME NEW x \in TranClosure(M) PROVE x \in allmessages  OBVIOUS
  <2>1. PICK mm \in M : x \in Tran(mm)  BY DEF TranClosure
  <2>mam. mm \in allmessages  BY <2>1, <1>msub
  <2>mmsg. mm \in Messages  BY <2>mam, <1>amsub
  <2>cases. x = mm \/ x \in TranExclusive(mm)  BY <2>1 DEF Tran, TranExclusive
  <2>c1. CASE x = mm  BY <2>c1, <2>1, <1>msub
  <2>c2. CASE x \in TranExclusive(mm)
    <3>xmsg. x \in Messages  BY <1>mmsg, <1>mi, TranClosureClosed
    <3>dm. <>(mm \in Msgs)
      <4>1. mm \in allmessages <=> IAMESCond(mm)  BY DEF IsAllMessagesEverSent
      <4> QED  BY <2>mam, <4>1 DEF IAMESCond
    <3>btcop. BTCop(mm, x)  BY <2>mmsg, <2>c2, BoxTranClosed
    <3>btc. [](({mm} \subseteq Msgs) => x \in Msgs)  BY <3>btcop DEF BTCop
    <3>nbop. NBop(mm)  BY NetBridge
    <3>nbx. [](({mm} \subseteq Msgs) <=> (mm \in Msgs))  BY <3>nbop DEF NBop
    <3>dx. <>(x \in Msgs)  BY <3>dm, <3>btc, <3>nbx, PTL
    <3>1b. x \in allmessages <=> IAMESCond(x)  BY DEF IsAllMessagesEverSent
    <3> QED  BY <3>xmsg, <3>dx, <3>1b DEF IAMESCond
  <2> QED  BY <2>cases, <2>c1, <2>c2
<1>balls. \A x \in TranClosure(M) : B(x) <= bal
  <2> SUFFICES ASSUME NEW x \in TranClosure(M) PROVE B(x) <= bal  OBVIOUS
  <2>1. PICK mm \in M : x \in Tran(mm)  BY DEF TranClosure
  <2>mmsg. mm \in Messages  BY <2>1, <1>msub, <1>amsub
  <2>mbal. B(mm) <= bal  BY <2>1
  <2>bx. B(x) <= B(mm)  BY <2>1, <2>mmsg, <1>mi, BMonotone
  <2>xmsg. x \in Messages  BY <1>mmsg, <1>mi, TranClosureClosed
  <2>bxb. B(x) \in Ballots  BY <2>xmsg, <1>mi, BBallot
  <2>bmb. B(mm) \in Ballots  BY <2>mmsg, <1>mi, BBallot
  <2> QED  BY <2>mbal, <2>bx, <2>bxb, <2>bmb DEF Ballots
<1>con. alpha \in ConFromCaught(alpha, CaughtS(TranClosure(M)))
  <2>snci. SafeAcceptors \cap CaughtS(allmessages) = {}  BY SafeAcceptorsNeverCaughtInfinite
  <2>tcmono. CaughtS(TranClosure(M)) \subseteq CaughtS(allmessages)  BY <1>tcsub, CaughtSMonoT
  <2>disj. SafeAcceptors \cap CaughtS(TranClosure(M)) = {}  BY <2>snci, <2>tcmono
  <2>pair. {alpha, alpha} = {alpha}  OBVIOUS
  <2>ss. SafeAcceptors \in SafetySets({alpha, alpha})  BY <2>pair
  <2> QED  BY <2>disj, <2>ss DEF ConFromCaught
<1>tcm. TranClosure(M) = M
  <2>sub2. M \subseteq TranClosure(M)  BY TranClosureExpanding
  <2>sub1. TranClosure(M) \subseteq M
    <3> SUFFICES ASSUME NEW z \in TranClosure(M) PROVE z \in M  OBVIOUS
    <3>za. z \in allmessages  BY <1>tcsub
    <3>zb. B(z) <= bal  BY <1>balls
    <3> QED  BY <3>za, <3>zb
  <2> QED  BY <2>sub1, <2>sub2
<1>teq. DecideableProposalTranExclusive(M) \subseteq Tran(p)  OBVIOUS
<1>vp. V(p) = DecideableProposalV(alpha, bal, M)
  <2>1. (IsProposal(p) /\ (B(p) > bal)) =>
          (/\ V(p) = DecideableProposalV(alpha, bal, {m \in allmessages : B(m) <= bal})
           /\ ((B(p) < B(p)) \/ (p = p)))
    OBVIOUS
  <2> QED  BY <2>1
<1>coneq. ConFromCaught(alpha, CaughtS({ww \in allmessages : B(ww) < B(p)}))
            = ConFromCaught(alpha, CaughtS(TranClosure(M)))
  <2>seteq. {ww \in allmessages : B(ww) < B(p)} = {m \in allmessages : B(m) < B(p)}  OBVIOUS
  <2>1. CaughtS(TranClosure(M)) = CaughtS(M)  BY <1>tcm
  <2> QED  BY <2>1, <2>seteq
<1>uniqrel. \A x \in allmessages : ((IsProposal(x) /\ (B(x) > bal)) =>
              ((V(x) = V(p)) /\ ((B(x) < B(p)) \/ (x = p))))
  <2> SUFFICES ASSUME NEW x \in allmessages, IsProposal(x), B(x) > bal
               PROVE (V(x) = V(p)) /\ ((B(x) < B(p)) \/ (x = p))  OBVIOUS
  <2>1. /\ V(x) = DecideableProposalV(alpha, bal, {m \in allmessages : B(m) <= bal})
        /\ ((B(x) < B(p)) \/ (x = p))
    OBVIOUS
  <2> QED  BY <2>1, <1>vp
<1>ind. \A d \in 0..MaxDepth(alpha) :
          LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), d)
  BY <1>amsub, <1>pprop, <1>teq, <1>vp, <1>con, <1>balls, <1>bpbal, <1>uniqrel, <1>coneq,
     TerminatingProposalTwoAInductionR
<1>lg. /\ FiniteAcceptors /\ LearnersNonEmpty /\ QuorumsNonEmpty
       /\ LearnersMightAgree /\ ValidLearnerGraphAssumption
  BY DEF LearnerGraphAssumptions
<1>mdrange. MaxDepth(alpha) \in 1..Cardinality(Acceptors)  BY <1>lg, MaxDepthFiniteAcceptors
<1>facc. IsFiniteSet(Acceptors)  BY DEF FiniteAcceptors, LearnerGraphAssumptions
<1>cardnat. Cardinality(Acceptors) \in Nat  BY <1>facc, FS_CardinalityType
<1>mdn. MaxDepth(alpha) \in Nat  BY <1>mdrange, <1>cardnat
<1>mdin. MaxDepth(alpha) \in 0..MaxDepth(alpha)  BY <1>mdn
<1>lasdb. LiveAcceptorsSentDepthBallot(allmessages, alpha, B(p), MaxDepth(alpha))
  BY <1>ind, <1>mdin
<1>decop. LASDBDecOp(alpha, allmessages, B(p))
  BY <1>amsub, <1>bpbal, <1>lasdb, LASDBDecisionW
<1> QED  BY <1>decop DEF LASDBDecOp
====================================================================
