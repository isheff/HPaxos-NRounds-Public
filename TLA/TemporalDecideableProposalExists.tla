------------------- MODULE TemporalDecideableProposalExists -------------------
EXTENDS HPaxosPlusCal,
        BMonotone, TranSubMessages, BBallot, LeTransBallotsT,
        BetaStarExists, TopLearnerMsgCorrect, TranClosureClosed, PExists

THEOREM TemporalDecideableProposalExists ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ ValueInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ NetworkAssumption
  ) =>
  \A alpha \in Learners :
  \A bal \in Ballots :
  \* M are all the ever-sent messages with bal or lower.  We take M over an
  \* abstract IsAllMessagesEverKnown set so the defining predicate (B(m) <= bal)
  \* is non-temporal -- no <> inside the set-builder (keeps SANY level-clean).
  \A allmessages :
  IsAllMessagesEverKnown(allmessages) =>
  LET M == {m \in allmessages : B(m) <= bal}
  IN \E p \in Proposals :
     (/\ TranExclusive(p) = DecideableProposalTranExclusive(M)
      /\ V(p) = DecideableProposalV(alpha, bal, M)
      /\ B(p) > bal
      /\ Sig(p) \notin Acceptors)
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, ValueInterfaceAssumptions,
                    LearnerGraphAssumptions, NetworkAssumption,
                    NEW alpha \in Learners, NEW bal \in Ballots,
                    NEW allmessages, IsAllMessagesEverKnown(allmessages)
             PROVE LET M == {m \in allmessages : B(m) <= bal}
                   IN \E p \in Proposals :
                      (/\ TranExclusive(p) = DecideableProposalTranExclusive(M)
                       /\ V(p) = DecideableProposalV(alpha, bal, M)
                       /\ B(p) > bal
                       /\ Sig(p) \notin Acceptors)
  OBVIOUS
<1> DEFINE M == {m \in allmessages : B(m) <= bal}
<1>amsub. allmessages \subseteq Messages
  <2> SUFFICES ASSUME NEW mm \in allmessages PROVE mm \in Messages  OBVIOUS
  <2>1. mm \in allmessages <=> IAMEKCond(mm)  BY DEF IsAllMessagesEverKnown
  <2> QED  BY <2>1 DEF IAMEKCond
<1>Msub. M \subseteq Messages  BY <1>amsub
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bp1nat. bal+1 \in Nat  BY <1>balnat
<1>bp1bal. bal+1 \in Ballots  BY <1>bp1nat DEF Ballots
<1>bound. \A y \in TranClosure(M) : B(y) < bal+1
  <2> SUFFICES ASSUME NEW y \in TranClosure(M) PROVE B(y) < bal+1  OBVIOUS
  <2>1. PICK m \in M : y \in Tran(m)  BY DEF TranClosure
  <2>2. m \in Messages /\ B(m) <= bal  BY <2>1, <1>amsub
  <2>3. B(y) <= B(m)  BY <2>1, <2>2, <1>mi, BMonotone
  <2>ym. y \in Messages  BY <2>1, <2>2, <1>mi, TranSubMessages
  <2>ybal. B(y) \in Ballots  BY <2>ym, <1>mi, BBallot
  <2>mbal. B(m) \in Ballots  BY <2>2, <1>mi, BBallot
  <2>4. B(y) <= bal  BY <2>3, <2>2, <2>ybal, <2>mbal, <1>balnat, LeTransBallotsT
  <2> QED BY <2>4, <1>balnat, <2>ybal DEF Ballots
<1>via. AlwaysAValue  BY DEF ValueInterfaceAssumptions
<1> DEFINE S == ConFromCaught(alpha, CaughtS(TranClosure(M)))
<1> DEFINE SS == S \cap RelevantLearners(M)
<1>tval. DecideableProposalV(alpha, bal, M) \in Values
  <2>caseE. CASE SS = {}
    <3>1. DecideableProposalV(alpha,bal,M) = BalToVal(bal)  BY <2>caseE DEF DecideableProposalV
    <3> QED BY <3>1, <1>via, <1>balnat DEF AlwaysAValue
  <2>caseNE. CASE SS # {}
    <3>ssL. SS \in SUBSET Learners
      <4>1. RelevantLearners(M) \subseteq Learners  BY DEF RelevantLearners
      <4> QED BY <4>1
    <3>ssrel. \A beta \in SS : \E x \in TranClosure(M) : beta \in Lrns(x)
      <4> SUFFICES ASSUME NEW beta \in SS PROVE \E x \in TranClosure(M) : beta \in Lrns(x)  OBVIOUS
      <4>1. beta \in RelevantLearners(M)  OBVIOUS
      <4> QED BY <4>1 DEF RelevantLearners
    <3>bse. \E beta \in SS : \A gamma \in SS : BXBeta(M,gamma) <= BXBeta(M,beta)
      BY <3>ssL, <2>caseNE, <3>ssrel, <1>bp1nat, <1>bound, <1>Msub, BetaStarExists
    <3> DEFINE betastar == CHOOSE beta \in SS : \A gamma \in SS : BXBeta(M,gamma) <= BXBeta(M,beta)
    <3>bsprop. betastar \in SS /\ (\A gamma \in SS : BXBeta(M,gamma) <= BXBeta(M,betastar))
      BY <3>bse
    <3>bsRel. betastar \in RelevantLearners(M)  BY <3>bsprop
    <3>xbmsgs. TopLearnerMsg(M,betastar) \in TranClosure(M)
      <4>ex. \E x \in TranClosure(M) : betastar \in Lrns(x)  BY <3>bsRel DEF RelevantLearners
      <4> QED BY <4>ex, <1>mi, <1>bp1nat, <1>bound, <1>Msub, TopLearnerMsgCorrect
    <3>xbm. TopLearnerMsg(M,betastar) \in Messages  BY <3>xbmsgs, <1>mi, <1>Msub, TranClosureClosed
    <3>vval. V(TopLearnerMsg(M,betastar)) \in Values
      <4>1. B(TopLearnerMsg(M,betastar)) \in Ballots  BY <3>xbm, <1>mi, BBallot
      <4> QED BY <4>1, <1>via DEF V, AlwaysAValue
    <3>dpv. DecideableProposalV(alpha,bal,M) = V(TopLearnerMsg(M,betastar))
      BY <2>caseNE DEF DecideableProposalV
    <3> QED BY <3>dpv, <3>vval
  <2> QED BY <2>caseE, <2>caseNE
<1>pex. \E p \in Proposals :
          /\ TranExclusive(p) = TranClosure(CQ(M))
          /\ B(p) > bal+1
          /\ Sig(p) \notin Acceptors
          /\ V(p) = DecideableProposalV(alpha, bal, M)
  BY <1>Msub, <1>bp1bal, <1>tval, <1>bound, MessageInterfaceAssumptions, LearnerGraphAssumptions,
     ValueInterfaceAssumptions, PExists
<1> PICK p \in Proposals :
      /\ TranExclusive(p) = TranClosure(CQ(M))
      /\ B(p) > bal+1
      /\ Sig(p) \notin Acceptors
      /\ V(p) = DecideableProposalV(alpha, bal, M)
  BY <1>pex
<1>pm. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>pbal. B(p) \in Ballots  BY <1>pm, <1>mi, BBallot
<1>pgtbal. B(p) > bal  BY <1>balnat, <1>bp1nat, <1>pbal DEF Ballots
<1> QED BY <1>pgtbal DEF DecideableProposalTranExclusive
====================================================================
