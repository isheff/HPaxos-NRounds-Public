------------------ MODULE DecideableProposalOneBFreshAny ------------------
EXTENDS MessageInterface, FiniteSetTheorems,
        BBallot, TranClosureClosed, CQSubTC,
        TranClosureAbsorb, TranClosureIdempotent, TranClosureUnion,
        TranClosureSingleton, TranClosureExpanding,
        MaxBSetProperty, ProposalBalLeB, BOfAbsorbing,
        CaughtSAddNonAcceptor, CaughtSAddOne, CatchWitnessCorrect,
        BetaStarExists, TopLearnerMsgCorrect

\* Any-witness companion to DecideableProposalOneBExists: given a message oneb
\* (not necessarily the one OneBExists/AlwaysANewOneB happens to construct)
\* whose TranExclusive matches the known-plus-p shape, oneb's B/IsOneB/Fresh
\* are all determined purely by that shape -- independent of how oneb came to
\* exist.
THEOREM DecideableProposalOneBFreshAny ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         \A x \in TranClosure(m) : B(x) <= bal,
         NEW p \in Proposals,
         TranExclusive(p) = DecideableProposalTranExclusive(m),
         B(p) > bal,
         Sig(p) \notin Acceptors,
         V(p) = DecideableProposalV(alpha, bal, m),
         NEW known \in SUBSET TranClosure(m),
         NEW a \in Acceptors, NEW oneb \in (Messages \ Proposals), Sig(oneb) = a,
         TranExclusive(oneb) = TranClosure(known \cup {p}),
         Sig(oneb) \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
  PROVE /\ B(oneb) = B(p)
        /\ IsOneB(oneb)
        /\ Fresh(alpha, oneb)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal
  BY DEF MessageInterfaceAssumptions
<1>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>btnat. B(p) \in Ballots  BY <1>pmsg, <1>mi, BBallot
<1> DEFINE btarg == B(p)
<1>balnat. bal \in Nat  BY DEF Ballots
<1>btargnat. btarg \in Nat  BY <1>btnat DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) <= bal  OBVIOUS
<1>baltbarg. bal < btarg  OBVIOUS
<1>boundt. \A x \in TranClosure(m) : B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(m) PROVE B(x) < btarg  OBVIOUS
  <2>le. B(x) <= bal  BY <1>bound
  <2>xm. x \in Messages  BY <1>mi, TranClosureClosed
  <2>bx. B(x) \in Ballots  BY <2>xm, <1>mi, BBallot
  <2> QED  BY <2>le, <2>bx, <1>baltbarg, <1>balnat, <1>btnat DEF Ballots
<1>tepeq. TranExclusive(p) = TranClosure(CQ(m))  BY DEF DecideableProposalTranExclusive
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>btargnat, <1>boundt, CQSubTC
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>csub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>tepsub. TranExclusive(p) \subseteq TranClosure(m)  BY <1>tepeq, <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
<1>tepidem. TranClosure(TranExclusive(p)) = TranExclusive(p)
  BY <1>tepeq, <1>cqmsgs, <1>mi, TranClosureIdempotent
<1>knownmsgs. known \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in known PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  OBVIOUS
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>knownsub. TranClosure(known) \subseteq TranClosure(m)  BY <1>mi, <1>knownmsgs, TranClosureAbsorb
<1>tc1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranExclusive(p)
  <2>1. TranClosure(known \cup TranExclusive(p)) = TranClosure(known) \cup TranClosure(TranExclusive(p))
    BY TranClosureUnion
  <2> QED BY <2>1, <1>tepidem
<1>tc2. TranClosure(known \cup {p}) = TranClosure(known) \cup Tran(p)
  <2>1. TranClosure(known \cup {p}) = TranClosure(known) \cup TranClosure({p})  BY TranClosureUnion
  <2>2. TranClosure({p}) = Tran(p)  BY TranClosureSingleton
  <2> QED BY <2>1, <2>2
<1>tranp. Tran(p) = {p} \cup TranExclusive(p)  BY DEF Tran, TranExclusive
<1>tc3. TranClosure(known \cup {p}) = TranClosure(known \cup TranExclusive(p)) \cup {p}
  BY <1>tc1, <1>tc2, <1>tranp
<1>oldballs. \A x \in TranClosure(known \cup TranExclusive(p)) : B(x) < btarg
  BY <1>tc1, <1>knownsub, <1>tepsub, <1>boundt
<1>ktepmsgs. TranClosure(known \cup TranExclusive(p)) \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in TranClosure(known \cup TranExclusive(p)) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>tc1, <1>knownsub, <1>tepsub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>kpmsgs. TranClosure(known \cup {p}) \subseteq Messages  BY <1>tc3, <1>ktepmsgs, <1>pmsg
<1>onebnotprop. oneb \notin Proposals  OBVIOUS
<1>onebmsg. oneb \in Messages  OBVIOUS
<1>pnotoneb. p # oneb  BY <1>onebnotprop
<1>cqoldballs. \A x \in TranClosure(CQ(m)) : B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(CQ(m)) PROVE B(x) < btarg  OBVIOUS
  <2>1. x \in TranClosure(m)  BY <1>csub, <1>mi, <1>cqmsgs, TranClosureAbsorb
  <2> QED  BY <2>1, <1>boundt
<1>bpbtarg. B(p) = btarg  OBVIOUS
<1>pbalp. ProposalBal(p) = btarg
  <2>propsub. Proposals \subseteq Messages  BY <1>mi DEF TypeOKMessageInterface
  <2>pgp. p \in GetProposals(p)
    <3>1. p \in Tran(p)  BY DEF Tran
    <3> QED BY <3>1 DEF GetProposals
  <2>fin. IsFiniteSet(GetProposals(p))
    <3>1. GetProposals(p) \subseteq Tran(p)  BY DEF GetProposals
    <3>2. IsFiniteSet(Tran(p))  BY <1>pmsg, <1>mi DEF TranFinite
    <3> QED BY <3>1, <3>2, FS_Subset
  <2>ne. GetProposals(p) # {}  BY <2>pgp
  <2>sub. GetProposals(p) \subseteq Proposals  BY DEF GetProposals
  <2>choose. /\ B(p) \in {ProposalBal(z) : z \in GetProposals(p)}
             /\ \A w \in {ProposalBal(z) : z \in GetProposals(p)} : B(p) >= w
    BY <1>mi, <2>fin, <2>sub, <2>ne, MaxBSetProperty DEF B
  <2> PICK z \in GetProposals(p) : B(p) = ProposalBal(z)  BY <2>choose
  <2>zgp. z \in Proposals /\ z \in Tran(p)  BY DEF GetProposals
  <2>zcase. z = p \/ z \in TranExclusive(p)  BY <2>zgp DEF TranExclusive
  <2>notother. z \in TranExclusive(p) => FALSE
    <3> SUFFICES ASSUME z \in TranExclusive(p) PROVE FALSE  OBVIOUS
    <3>1. z \in TranClosure(CQ(m))  BY <1>tepeq
    <3>2. B(z) < btarg  BY <3>1, <1>cqoldballs
    <3>3. ProposalBal(z) <= B(z)  BY <2>zgp, ProposalBalLeB
    <3>4. ProposalBal(z) = B(p)  BY <2>choose
    <3>5. B(p) = btarg  OBVIOUS
    <3>zmsg. z \in Messages  BY <2>zgp, <1>mi DEF TypeOKMessageInterface
    <3>pbz. ProposalBal(z) \in Ballots  BY <2>zgp, <1>mi DEF TypeOKMessageInterface, ProposalBal
    <3>bz. B(z) \in Ballots  BY <3>zmsg, <1>mi, BBallot
    <3>bp. B(p) \in Ballots  BY <1>btnat
    <3> QED BY <3>2, <3>3, <3>4, <3>5, <3>pbz, <3>bz, <3>bp DEF Ballots
  <2>zisp. z = p  BY <2>zcase, <2>notother
  <2> QED BY <2>choose, <2>zisp
<1>notpballs. \A x \in TranClosure(known \cup {p}) : x # p => B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), x # p PROVE B(x) < btarg  OBVIOUS
  <2>1. x \in TranClosure(known \cup TranExclusive(p))  BY <1>tc3
  <2> QED  BY <2>1, <1>oldballs
<1>pinS. p \in TranClosure(known \cup {p})
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1 DEF TranClosure
<1>Boneb. B(oneb) = btarg
  BY <1>onebmsg, <1>kpmsgs, <1>onebnotprop, <1>pinS, <1>pbalp, <1>notpballs, <1>btnat, BOfAbsorbing
<1>seteqp. {x \in TranClosure(known \cup {p}) : B(x) = btarg} = {p}
  <2> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), B(x) = btarg
               PROVE x = p
    BY <1>tc3
  <2>1. x \in TranClosure(known \cup TranExclusive(p)) \/ x = p  BY <1>tc3
  <2>2. CASE x = p  BY <2>2
  <2>3. CASE x \in TranClosure(known \cup TranExclusive(p))
    <3>1. B(x) < btarg  BY <2>3, <1>oldballs
    <3>2. x \in Messages  BY <2>3, <1>ktepmsgs
    <3>3. B(x) \in Ballots  BY <3>2, <1>mi, BBallot
    <3> QED BY <3>1, <3>3, <1>baltbarg, <1>balnat, <1>btnat DEF Ballots
  <2> QED BY <2>1, <2>2, <2>3
<1>tranoneb. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY DEF Tran, TranExclusive
<1>cardoneb2. Cardinality({z \in Tran(oneb) : B(z) = btarg}) = 2
  <2>seteq. {z \in Tran(oneb) : B(z) = btarg} = {oneb, p}
    BY <1>tranoneb, <1>seteqp, <1>Boneb, <1>pnotoneb
  <2>card2. Cardinality({oneb, p}) = 2
    <3>1. IsFiniteSet({p})  BY FS_Singleton
    <3>2. Cardinality({p}) = 1  BY FS_Singleton
    <3>3. oneb \notin {p}  BY <1>pnotoneb
    <3>4. {oneb,p} = {oneb} \cup {p}  OBVIOUS
    <3> QED BY <3>1, <3>2, <3>3, <3>4, FS_AddElement
  <2> QED BY <2>seteq, <2>card2
<1>isoneb. IsOneB(oneb)
  <2>1. {z \in Tran(oneb) : B(z) = B(oneb)} = {z \in Tran(oneb) : B(z) = btarg}  BY <1>Boneb
  <2>2. Cardinality({z \in Tran(oneb) : B(z) = B(oneb)}) = 2  BY <2>1, <1>cardoneb2
  <2>3. ~IsProposal(oneb)  BY <1>onebnotprop DEF IsProposal
  <2> QED BY <2>3, <2>2 DEF IsOneB
<1>caughtoneb. Caught(oneb) = CaughtS(TranClosure(m))
  <2>ctran. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY <1>tranoneb
  <2>step1. CaughtS(TranClosure(known \cup TranExclusive(p))) = CaughtS(TranClosure(m))
    <3>sub1. TranClosure(known \cup TranExclusive(p)) \subseteq TranClosure(m)
      BY <1>tc1, <1>knownsub, <1>tepsub
    <3>fwd. CaughtS(TranClosure(known \cup TranExclusive(p))) \subseteq CaughtS(TranClosure(m))
      BY <3>sub1 DEF CaughtS
    <3>bwd. CaughtS(TranClosure(m)) \subseteq CaughtS(TranClosure(known \cup TranExclusive(p)))
      <4> SUFFICES ASSUME NEW s \in CaughtS(TranClosure(m))
                   PROVE s \in CaughtS(TranClosure(known \cup TranExclusive(p)))
        OBVIOUS
      <4>w1. s \in CaughtAcc(m)  BY DEF CaughtAcc
      <4>w2. CatchWitness1(m,s) \in CQ(m) /\ CatchWitness2(m,s) \in CQ(m)  BY <4>w1 DEF CQ
      <4>w3. CatchWitness1(m,s) \in TranClosure(CQ(m)) /\ CatchWitness2(m,s) \in TranClosure(CQ(m))
        BY <4>w2, TranClosureExpanding
      <4>w4. CatchWitness1(m,s) \in TranExclusive(p) /\ CatchWitness2(m,s) \in TranExclusive(p)
        BY <4>w3, <1>tepeq
      <4>w5. /\ Sig(CatchWitness1(m,s)) = s /\ Sig(CatchWitness2(m,s)) = s
             /\ CatchWitness1(m,s) \notin Tran(CatchWitness2(m,s))
             /\ CatchWitness2(m,s) \notin Tran(CatchWitness1(m,s))
        BY <1>mi, <4>w1, CatchWitnessCorrect DEF CaughtAcc
      <4>w6. CatchWitness1(m,s) \in TranClosure(known \cup TranExclusive(p))
             /\ CatchWitness2(m,s) \in TranClosure(known \cup TranExclusive(p))
        BY <4>w4, TranClosureExpanding
      <4> QED BY <4>w5, <4>w6 DEF CaughtS
    <3> QED BY <3>fwd, <3>bwd
  <2>step2. CaughtS(TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup TranExclusive(p)))
    <3>1. CaughtS(TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
      BY <1>tc3
    <3>2. CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
            = CaughtS(TranClosure(known \cup TranExclusive(p)))
      BY <1>mi, <1>ktepmsgs, CaughtSAddNonAcceptor
    <3> QED BY <3>1, <3>2
  <2>step3. CaughtS({oneb} \cup TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup {p}))
    <3>comm. {oneb} \cup TranClosure(known \cup {p}) = TranClosure(known \cup {p}) \cup {oneb}  OBVIOUS
    <3>anot. Sig(oneb) \notin CaughtS(TranClosure(known \cup {p}))  BY <2>step2
    <3>anotoneb. Sig(oneb) \notin CaughtS(TranClosure(known \cup {p}) \cup {oneb})
      <4> SUFFICES ASSUME Sig(oneb) \in CaughtS(TranClosure(known \cup {p}) \cup {oneb}) PROVE FALSE
        OBVIOUS
      <4>1. PICK m1 \in (TranClosure(known \cup {p}) \cup {oneb}) :
              \E m2 \in (TranClosure(known \cup {p}) \cup {oneb}) :
                Sig(m1) = Sig(oneb) /\ Sig(m2) = Sig(oneb) /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
        BY DEF CaughtS
      <4>2. PICK m2 \in (TranClosure(known \cup {p}) \cup {oneb}) :
              Sig(m1) = Sig(oneb) /\ Sig(m2) = Sig(oneb) /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
        BY <4>1
      <4>m1case. m1 = oneb \/ m1 \in TranClosure(known \cup {p})  BY <4>2
      <4>m2case. m2 = oneb \/ m2 \in TranClosure(known \cup {p})  BY <4>2
      <4>notboth. ~(m1 = oneb /\ m2 = oneb)
        <5> SUFFICES ASSUME m1 = oneb, m2 = oneb PROVE FALSE  OBVIOUS
        <5>1. m1 \in Tran(m2)  BY DEF Tran
        <5> QED BY <5>1, <4>2
      <4>m1oneb. CASE m1 = oneb
        <5>m2old. m2 \in TranClosure(known \cup {p})  BY <4>m1oneb, <4>notboth, <4>m2case
        <5>m2te. m2 \in TranExclusive(oneb)  BY <5>m2old
        <5>m2tr. m2 \in Tran(oneb)  BY <5>m2te DEF TranExclusive
        <5>m2trm1. m2 \in Tran(m1)  BY <5>m2tr, <4>m1oneb
        <5> QED BY <5>m2trm1, <4>2
      <4>m2oneb. CASE m2 = oneb
        <5>m1old. m1 \in TranClosure(known \cup {p})  BY <4>m2oneb, <4>notboth, <4>m1case
        <5>m1te. m1 \in TranExclusive(oneb)  BY <5>m1old
        <5>m1tr. m1 \in Tran(oneb)  BY <5>m1te DEF TranExclusive
        <5>m1trm2. m1 \in Tran(m2)  BY <5>m1tr, <4>m2oneb
        <5> QED BY <5>m1trm2, <4>2
      <4>bothold. CASE m1 \in TranClosure(known \cup {p}) /\ m2 \in TranClosure(known \cup {p})
        <5>caught. Sig(oneb) \in CaughtS(TranClosure(known \cup {p}))
          BY <4>2, <4>bothold DEF CaughtS
        <5> QED BY <5>caught, <3>anot
      <4>alldisj. m1 = oneb \/ m2 = oneb
                    \/ (m1 \in TranClosure(known \cup {p}) /\ m2 \in TranClosure(known \cup {p}))
        BY <4>m1case, <4>m2case
      <4> QED BY <4>alldisj, <4>m1oneb, <4>m2oneb, <4>bothold
    <3>eq. CaughtS(TranClosure(known \cup {p}) \cup {oneb}) = CaughtS(TranClosure(known \cup {p}))
      <4>facc. Sig(oneb) \in Acceptors \/ Sig(oneb) \notin Acceptors  OBVIOUS
      <4>a. CASE Sig(oneb) \in Acceptors
        BY <1>mi, <1>kpmsgs, <3>anotoneb, <4>a, CaughtSAddOne
      <4>b. CASE Sig(oneb) \notin Acceptors
        BY <1>mi, <1>kpmsgs, <4>b, CaughtSAddNonAcceptor
      <4> QED BY <4>facc, <4>a, <4>b
    <3> QED BY <3>comm, <3>eq
  <2> QED BY <2>ctran, <2>step1, <2>step2, <2>step3 DEF Caught
<1> DEFINE S == ConFromCaught(alpha, CaughtS(TranClosure(m)))
<1> DEFINE SS == S \cap RelevantLearners(m)
<1>fresh. Fresh(alpha, oneb)
  <2>caseNE. CASE SS # {}
    <3>ssL. SS \in SUBSET Learners
      <4>1. RelevantLearners(m) \subseteq Learners  BY DEF RelevantLearners
      <4> QED BY <4>1
    <3>ssrel. \A beta \in SS : \E x \in TranClosure(m) : beta \in Lrns(x)
      <4> SUFFICES ASSUME NEW beta \in SS PROVE \E x \in TranClosure(m) : beta \in Lrns(x)  OBVIOUS
      <4>1. beta \in RelevantLearners(m)  OBVIOUS
      <4> QED BY <4>1 DEF RelevantLearners
    <3>bse. \E beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
      BY <3>ssL, <2>caseNE, <3>ssrel, <1>btargnat, <1>boundt, BetaStarExists
    <3> DEFINE betastar == CHOOSE beta \in SS : \A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,beta)
    <3>bsprop. betastar \in SS /\ (\A gamma \in SS : BXBeta(m,gamma) <= BXBeta(m,betastar))
      BY <3>bse
    <3>bsS. betastar \in S  BY <3>bsprop
    <3>bsSraw. betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>bsS
    <3>bsRel. betastar \in RelevantLearners(m)  BY <3>bsprop
    <3>bstL. betastar \in Learners  BY <3>ssL, <3>bsprop
    <3>bsLrns. betastar \in Lrns(TopLearnerMsg(m,betastar))
      <4>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <3>bsRel DEF RelevantLearners
      <4> QED BY <4>ex, <1>mi, <1>btargnat, <1>boundt, TopLearnerMsgCorrect
    <3>bsMax. \A beta \in S : (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
      <4> SUFFICES ASSUME NEW beta \in S, \E x \in TranClosure(m) : beta \in Lrns(x)
                   PROVE BXBeta(m,beta) <= BXBeta(m,betastar)
        OBVIOUS
      <4>0. beta \in Learners  BY DEF ConFromCaught
      <4>1. beta \in RelevantLearners(m)  BY <4>0 DEF RelevantLearners
      <4>2. beta \in SS  BY <4>1
      <4> QED BY <4>2, <3>bsprop
    <3>bsMaxraw. \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                   (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
      BY <3>bsMax
    <3>xbmsgs. TopLearnerMsg(m,betastar) \in TranClosure(m)
      <4>ex. \E x \in TranClosure(m) : betastar \in Lrns(x)  BY <3>bsRel DEF RelevantLearners
      <4> QED BY <4>ex, <1>mi, <1>btargnat, <1>boundt, TopLearnerMsgCorrect
    <3>dpv. DecideableProposalV(alpha,bal,m) = V(TopLearnerMsg(m,betastar))
      BY <2>caseNE DEF DecideableProposalV
    <3>vp. V(p) = V(TopLearnerMsg(m,betastar))  BY <3>dpv
    <3>bsWit. \E bs \in Learners : bs = betastar  BY <3>bstL
    <3> PICK bs \in Learners : bs = betastar  BY <3>bsWit
    <3>bsSraw2. bs \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>bsSraw
    <3>xbmsgs2. TopLearnerMsg(m,bs) \in TranClosure(m)  BY <3>xbmsgs
    <3>bsLrns2. bs \in Lrns(TopLearnerMsg(m,bs))  BY <3>bsLrns
    <3>bsMaxraw2. \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                   (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,bs)
      BY <3>bsMaxraw
    <3>vp2. V(p) = V(TopLearnerMsg(m,bs))  BY <3>vp
    <3>bsRel2. bs \in RelevantLearners(m)  BY <3>bsRel
    <3>Vonebp. V(oneb) = V(p)  BY <1>Boneb, <1>bpbtarg DEF V
    <3>Voneb. V(oneb) = V(TopLearnerMsg(m,bs))  BY <3>Vonebp, <3>vp2
    <3>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>caughtoneb DEF Con
    <3>bsIn. bs \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>bsSraw2
    <3>xbetastarInCQ. TopLearnerMsg(m,bs) \in CQ(m)
      <4>rel. bs \in RelevantLearners(m)  BY <3>bsRel2
      <4> QED BY <4>rel DEF CQ
    <3>xbetastarInTEp. TopLearnerMsg(m,bs) \in TranExclusive(p)
      BY <3>xbetastarInCQ, TranClosureExpanding, <1>tepeq
    <3>xbetastarInKTEp. TopLearnerMsg(m,bs) \in TranClosure(known \cup TranExclusive(p))
      BY <3>xbetastarInTEp, TranClosureExpanding
    <3>xbetastarInOneb. TopLearnerMsg(m,bs) \in TranExclusive(oneb)
      BY <3>xbetastarInKTEp, <1>tc3
    <3> SUFFICES ASSUME NEW x \in Tran(oneb)
                 PROVE \/ V(x) = V(oneb)
                       \/ Con(alpha, oneb) \cap Lrns(x) = {}
                       \/ \E q \in TranExclusive(oneb) : B(q) > B(x) /\ Con(alpha, oneb) \cap Lrns(q) # {}
      BY DEF Fresh
    <3>xcase. x = oneb \/ x \in TranClosure(known \cup {p})  BY <1>tranoneb
    <3>caseA. CASE x = oneb  BY <3>caseA
    <3>caseB. CASE x \in TranClosure(known \cup {p})
      <4>xcase2. x = p \/ x \in TranClosure(known \cup TranExclusive(p))  BY <3>caseB, <1>tc3
      <4>caseBp. CASE x = p  BY <4>caseBp, <3>Vonebp
      <4>caseBo. CASE x \in TranClosure(known \cup TranExclusive(p))
        <5>xm. x \in TranClosure(m)  BY <4>caseBo, <1>tc1, <1>knownsub, <1>tepsub
        <5>xbal. B(x) < btarg  BY <4>caseBo, <1>oldballs
        <5>empty. CASE Con(alpha, oneb) \cap Lrns(x) = {}  BY <5>empty
        <5>nonempty. CASE Con(alpha, oneb) \cap Lrns(x) # {}
          <6> PICK beta \in Con(alpha, oneb) \cap Lrns(x) : TRUE  BY <5>nonempty
          <6>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>S
          <6>betaLrns. beta \in Lrns(x)  OBVIOUS
          <6>xb. TopLearnerMsg(m,beta) \in TranClosure(m)
                 /\ beta \in Lrns(TopLearnerMsg(m,beta))
                 /\ B(x) <= B(TopLearnerMsg(m,beta))
            <7>ex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <5>xm, <6>betaLrns
            <7> QED BY <7>ex, <5>xm, <6>betaLrns, <1>mi, <1>btargnat, <1>boundt, TopLearnerMsgCorrect
          <6>bxbeta. B(x) <= BXBeta(m,beta)  BY <6>xb DEF BXBeta
          <6>bxbetastar. BXBeta(m,beta) <= BXBeta(m,bs)
            <7>ex2. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <5>xm, <6>betaLrns
            <7> QED BY <3>bsMaxraw2, <6>betaS, <7>ex2
          <6>xmsg. x \in Messages  BY <5>xm, <1>mi, TranClosureClosed
          <6>bxnat. B(x) \in Ballots  BY <6>xmsg, <1>mi, BBallot
          <6>bxbmsg. TopLearnerMsg(m,beta) \in Messages  BY <6>xb, <1>mi, TranClosureClosed
          <6>bxbnat. BXBeta(m,beta) \in Ballots  BY <6>bxbmsg, <1>mi, BBallot DEF BXBeta
          <6>bxbsmsg. TopLearnerMsg(m,bs) \in TranClosure(m)  BY <3>xbmsgs2
          <6>bxbsmsg2. TopLearnerMsg(m,bs) \in Messages  BY <6>bxbsmsg, <1>mi, TranClosureClosed
          <6>bxbsnat. BXBeta(m,bs) \in Ballots  BY <6>bxbsmsg2, <1>mi, BBallot DEF BXBeta
          <6>ineq. B(x) <= BXBeta(m,bs)
            BY <6>bxbeta, <6>bxbetastar, <6>bxnat, <6>bxbnat, <6>bxbsnat DEF Ballots
          <6>caseTie. CASE B(x) = BXBeta(m,bs)
            <7>eq1. B(x) = B(TopLearnerMsg(m,bs))  BY <6>caseTie DEF BXBeta
            <7>samebal. V(x) = V(TopLearnerMsg(m,bs))  BY <7>eq1 DEF V
            <7> QED BY <7>samebal, <3>Voneb
          <6>caseStrict. CASE B(x) < BXBeta(m,bs)
            <7>bq. B(x) < B(TopLearnerMsg(m,bs))  BY <6>caseStrict DEF BXBeta
            <7>lrnsx. Con(alpha, oneb) \cap Lrns(TopLearnerMsg(m,bs)) # {}
              <8>1. bs \in Con(alpha, oneb)  BY <3>S, <3>bsIn
              <8>2. bs \in Lrns(TopLearnerMsg(m,bs))  BY <3>bsLrns2
              <8> QED BY <8>1, <8>2
            <7> QED BY <3>xbetastarInOneb, <7>bq, <7>lrnsx
          <6> QED BY <6>ineq, <6>caseTie, <6>caseStrict
        <5> QED BY <5>empty, <5>nonempty
      <4> QED BY <4>xcase2, <4>caseBp, <4>caseBo
    <3> QED BY <3>xcase, <3>caseA, <3>caseB
  <2>caseE. CASE SS = {}
    <3>capempty. S \cap RelevantLearners(m) = {}  BY <2>caseE
    <3>capemptyraw. ConFromCaught(alpha, CaughtS(TranClosure(m))) \cap RelevantLearners(m) = {}
      BY <3>capempty
    <3>Vonebp. V(oneb) = V(p)  BY <1>Boneb, <1>bpbtarg DEF V
    <3>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>caughtoneb DEF Con
    <3> SUFFICES ASSUME NEW x \in Tran(oneb)
                 PROVE \/ V(x) = V(oneb)
                       \/ Con(alpha, oneb) \cap Lrns(x) = {}
                       \/ \E q \in TranExclusive(oneb) : B(q) > B(x) /\ Con(alpha, oneb) \cap Lrns(q) # {}
      BY DEF Fresh
    <3>xcase. x = oneb \/ x \in TranClosure(known \cup {p})  BY <1>tranoneb
    <3>caseA. CASE x = oneb  BY <3>caseA
    <3>caseB. CASE x \in TranClosure(known \cup {p})
      <4>xcase2. x = p \/ x \in TranClosure(known \cup TranExclusive(p))  BY <3>caseB, <1>tc3
      <4>caseBp. CASE x = p  BY <4>caseBp, <3>Vonebp
      <4>caseBo. CASE x \in TranClosure(known \cup TranExclusive(p))
        <5>xm. x \in TranClosure(m)  BY <4>caseBo, <1>tc1, <1>knownsub, <1>tepsub
        <5>empty. Con(alpha, oneb) \cap Lrns(x) = {}
          <6> SUFFICES ASSUME NEW beta \in Con(alpha, oneb) \cap Lrns(x) PROVE FALSE  OBVIOUS
          <6>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>S
          <6>betaLearner. beta \in Learners  BY DEF Lrns
          <6>betaex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <5>xm
          <6>betaRel. beta \in RelevantLearners(m)  BY <6>betaLearner, <6>betaex DEF RelevantLearners
          <6> QED BY <6>betaS, <6>betaRel, <3>capemptyraw
        <5> QED BY <5>empty
      <4> QED BY <4>xcase2, <4>caseBp, <4>caseBo
    <3> QED BY <3>xcase, <3>caseA, <3>caseB
  <2> QED BY <2>caseNE, <2>caseE
<1> QED BY <1>Boneb, <1>isoneb, <1>fresh
====================================================================
