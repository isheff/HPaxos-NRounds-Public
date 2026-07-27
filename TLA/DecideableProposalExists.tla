--------------------- MODULE DecideableProposalExists ---------------------
\* Top of the DecideableProposal chain: the only THEOREM (not LEMMA) in the
\* split of MessageInterface.
EXTENDS MessageInterface,
        CQSubTC, TranClosureClosed, TranClosureAbsorb,
        DecideableProposalPExists, DecideableProposalOneBExists

THEOREM DecideableProposalExists ==
  (/\ MessageInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ ValueInterfaceAssumptions) =>
    \A alpha \in Learners :
    \A bal \in Ballots :
    \A m \in SUBSET Messages :
    (/\ alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
     /\ \A x \in TranClosure(m) : B(x) < bal
    ) => \E p \in Proposals :
         (/\ TranExclusive(p) \subseteq TranClosure(m)
          /\ B(p) > bal
          /\ \A a \in Acceptors:
             \A known \in SUBSET TranClosure(m):
             (/\ IsFiniteSet(known)
              /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
             )=>
               \E oneb \in Messages :
               (/\ Sig(oneb) = a
                /\ a \notin Caught(oneb)
                /\ IsOneB(oneb)
                /\ TranExclusive(oneb) = TranClosure(known \cup {p})
                /\ Fresh(alpha, oneb)
               )
         )
<1> SUFFICES ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
                    NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
                    alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
                    \A x \in TranClosure(m) : B(x) < bal
             PROVE \E p \in Proposals :
                     (/\ TranExclusive(p) \subseteq TranClosure(m)
                      /\ B(p) > bal
                      /\ \A a \in Acceptors:
                         \A known \in SUBSET TranClosure(m):
                         (/\ IsFiniteSet(known)
                          /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
                         )=>
                           \E oneb \in Messages :
                           (/\ Sig(oneb) = a
                            /\ a \notin Caught(oneb)
                            /\ IsOneB(oneb)
                            /\ TranExclusive(oneb) = TranClosure(known \cup {p})
                            /\ Fresh(alpha, oneb)
                           )
                     )
  OBVIOUS
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>pex. \E p \in Proposals :
          /\ TranExclusive(p) = DecideableProposalTranExclusive(m)
          /\ B(p) > bal
          /\ Sig(p) \notin Acceptors
          /\ V(p) = DecideableProposalV(alpha, bal, m)
  BY MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions, DecideableProposalPExists
<1> PICK p \in Proposals :
      /\ TranExclusive(p) = DecideableProposalTranExclusive(m)
      /\ B(p) > bal
      /\ Sig(p) \notin Acceptors
      /\ V(p) = DecideableProposalV(alpha, bal, m)
  BY <1>pex
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, CQSubTC
<1>tep. TranExclusive(p) = TranClosure(CQ(m))  BY DEF DecideableProposalTranExclusive
<1>tesub. TranExclusive(p) \subseteq TranClosure(m)  BY <1>tep, <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
<1>ex1. \A a \in Acceptors :
          \A known \in SUBSET TranClosure(m) :
            (/\ IsFiniteSet(known) /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p))))
            => \E oneb \in Messages :
                 (/\ Sig(oneb) = a /\ a \notin Caught(oneb) /\ IsOneB(oneb)
                  /\ TranExclusive(oneb) = TranClosure(known \cup {p}) /\ Fresh(alpha, oneb))
  BY MessageInterfaceAssumptions, LearnerGraphAssumptions, DecideableProposalOneBExists
<1> QED BY <1>tesub, <1>ex1
====================================================================
