--------------------- MODULE DecideableProposalOneBFreshR ---------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        BBallot, TranClosureClosed, TranClosureExpanding, TranClosureAbsorb,
        CQSubTC, ProposalBalLeB, BOfAbsorbing, CaughtSAddOne, CatchWitnessCorrect,
        MaxBSetProperty, BetaStarExists, TopLearnerMsgCorrect, CFCAntitoneR

\* Relaxed freshness engine: any-witness B/IsOneB/Fresh for a 1B whose history
\* is the mixed-ballot TranClosure(known \cup {p}) -- low part inside
\* TranClosure(m), high part V(p)-valued strictly below B(p) -- with p's
\* history merely CONTAINING DecideableProposalTranExclusive(m), and the 1B's
\* connectivity view pinned to the DPV view by the CS2 sandwich.
LEMMA DecideableProposalOneBFreshR ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         alpha \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         \A x \in TranClosure(m) : B(x) <= bal,
         NEW p \in Proposals,
         DecideableProposalTranExclusive(m) \subseteq Tran(p),
         B(p) > bal,
         Sig(p) \notin Acceptors,
         V(p) = DecideableProposalV(alpha, bal, m),
         NEW known \in SUBSET Messages,
         \A w \in TranClosure(known \cup {p}) :
           (w # p) => (\/ ((B(w) <= bal) /\ (w \in TranClosure(m)))
                       \/ ((B(w) > bal) /\ (B(w) < B(p)) /\ (V(w) = V(p)))),
         NEW CS2,
         CaughtS(TranClosure(known \cup {p})) \subseteq CS2,
         ConFromCaught(alpha, CS2) = ConFromCaught(alpha, CaughtS(TranClosure(m))),
         NEW a \in Acceptors, NEW oneb \in (Messages \ Proposals), Sig(oneb) = a,
         TranExclusive(oneb) = TranClosure(known \cup {p}),
         a \notin CaughtS(TranClosure(known \cup {p}))
  PROVE /\ B(oneb) = B(p)
        /\ IsOneB(oneb)
        /\ Fresh(alpha, oneb)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal /\ TranAcyclic
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
<1>dpte. TranClosure(CQ(m)) \subseteq Tran(p)  BY DEF DecideableProposalTranExclusive
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>btargnat, <1>boundt, CQSubTC
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>csub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>pnotm. p \notin TranClosure(m)
  <2> SUFFICES ASSUME p \in TranClosure(m) PROVE FALSE  OBVIOUS
  <2>1. B(p) <= bal  BY <1>bound
  <2> QED BY <2>1, <1>baltbarg, <1>btnat, <1>balnat DEF Ballots
<1>cqsubTEp. TranClosure(CQ(m)) \subseteq TranExclusive(p)
  <2>1. TranClosure(CQ(m)) \subseteq TranClosure(m)
    BY <1>csub, <1>cqmsgs, <1>mi, TranClosureAbsorb
  <2>2. \A z \in TranClosure(CQ(m)) : z # p  BY <2>1, <1>pnotm
  <2>tranp. Tran(p) = {p} \cup TranExclusive(p)  BY DEF Tran, TranExclusive
  <2> QED BY <1>dpte, <2>2, <2>tranp
<1>knownmsgs. known \in SUBSET Messages  OBVIOUS
<1>kpmsgs0. known \cup {p} \in SUBSET Messages  BY <1>knownmsgs, <1>pmsg
<1>tcKP. TranClosure(known \cup {p}) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in TranClosure(known \cup {p}) PROVE z \in Messages  OBVIOUS
  <2> QED BY <1>kpmsgs0, <1>mi, TranClosureClosed
<1>notpballs. \A x \in TranClosure(known \cup {p}) : x # p => B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), x # p PROVE B(x) < btarg  OBVIOUS
  <2>cl. \/ ((B(x) <= bal) /\ (x \in TranClosure(m)))
         \/ ((B(x) > bal) /\ (B(x) < B(p)) /\ (V(x) = V(p)))
    OBVIOUS
  <2>xmsg. x \in Messages  BY <1>tcKP
  <2>bx. B(x) \in Ballots  BY <2>xmsg, <1>mi, BBallot
  <2>c1. CASE (B(x) <= bal) /\ (x \in TranClosure(m))
    BY <2>c1, <1>baltbarg, <2>bx, <1>balnat, <1>btnat DEF Ballots
  <2>c2. CASE (B(x) > bal) /\ (B(x) < B(p)) /\ (V(x) = V(p))  BY <2>c2
  <2> QED BY <2>cl, <2>c1, <2>c2
<1>onebnotprop. oneb \notin Proposals  OBVIOUS
<1>onebmsg. oneb \in Messages  OBVIOUS
<1>pnotoneb. p # oneb  BY <1>onebnotprop
<1>tepsub2. TranExclusive(p) \subseteq TranClosure(known \cup {p})
  <2>a. p \in known \cup {p}  OBVIOUS
  <2>b. Tran(p) \subseteq TranClosure(known \cup {p})  BY <2>a DEF TranClosure
  <2>c. TranExclusive(p) \subseteq Tran(p)  BY DEF Tran, TranExclusive
  <2> QED BY <2>b, <2>c
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
    <3>1. z \in TranClosure(known \cup {p})  BY <1>tepsub2
    <3>znotp. z # p
      <4> SUFFICES ASSUME z = p PROVE FALSE  OBVIOUS
      <4>1. p \in TranExclusive(p)  OBVIOUS
      <4>2. p \in Tran(p)  BY DEF Tran
      <4> QED BY <4>1, <4>2, <1>pmsg, <1>mi DEF TranAcyclic
    <3>2. B(z) < btarg  BY <3>1, <3>znotp, <1>notpballs
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
<1>pinS. p \in TranClosure(known \cup {p})
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1 DEF TranClosure
<1>Boneb. B(oneb) = btarg
  BY <1>onebmsg, <1>tcKP, <1>onebnotprop, <1>pinS, <1>pbalp, <1>notpballs, <1>btnat, BOfAbsorbing
<1>seteqp. {x \in TranClosure(known \cup {p}) : B(x) = btarg} = {p}
  <2>in. p \in {x \in TranClosure(known \cup {p}) : B(x) = btarg}
    BY <1>pinS, <1>bpbtarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), B(x) = btarg
               PROVE x = p
    BY <2>in
  <2>1. CASE x = p  BY <2>1
  <2>2. CASE x # p
    <3>1. B(x) < btarg  BY <2>2, <1>notpballs
    <3>2. x \in Messages  BY <1>tcKP
    <3>3. B(x) \in Ballots  BY <3>2, <1>mi, BBallot
    <3> QED BY <3>1, <3>3, <1>btnat DEF Ballots
  <2> QED BY <2>1, <2>2
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
<1>caughteq. Caught(oneb) = CaughtS(TranClosure(known \cup {p}))
  <2>ctran. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY <1>tranoneb
  <2>anot. a \notin CaughtS(TranClosure(known \cup {p}))  OBVIOUS
  <2>anotoneb. a \notin CaughtS(TranClosure(known \cup {p}) \cup {oneb})
    <3> SUFFICES ASSUME a \in CaughtS(TranClosure(known \cup {p}) \cup {oneb}) PROVE FALSE
      OBVIOUS
    <3>1. PICK m1 \in (TranClosure(known \cup {p}) \cup {oneb}) :
            \E m2 \in (TranClosure(known \cup {p}) \cup {oneb}) :
              Sig(m1) = a /\ Sig(m2) = a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY DEF CaughtS
    <3>2. PICK m2 \in (TranClosure(known \cup {p}) \cup {oneb}) :
            Sig(m1) = a /\ Sig(m2) = a /\ m1 \notin Tran(m2) /\ m2 \notin Tran(m1)
      BY <3>1
    <3>m1case. m1 = oneb \/ m1 \in TranClosure(known \cup {p})  BY <3>2
    <3>m2case. m2 = oneb \/ m2 \in TranClosure(known \cup {p})  BY <3>2
    <3>notboth. ~(m1 = oneb /\ m2 = oneb)
      <4> SUFFICES ASSUME m1 = oneb, m2 = oneb PROVE FALSE  OBVIOUS
      <4>1. m1 \in Tran(m2)  BY DEF Tran
      <4> QED BY <4>1, <3>2
    <3>m1oneb. CASE m1 = oneb
      <4>m2old. m2 \in TranClosure(known \cup {p})  BY <3>m1oneb, <3>notboth, <3>m2case
      <4>m2te. m2 \in TranExclusive(oneb)  BY <4>m2old
      <4>m2tr. m2 \in Tran(oneb)  BY <4>m2te DEF TranExclusive
      <4>m2trm1. m2 \in Tran(m1)  BY <4>m2tr, <3>m1oneb
      <4> QED BY <4>m2trm1, <3>2
    <3>m2oneb. CASE m2 = oneb
      <4>m1old. m1 \in TranClosure(known \cup {p})  BY <3>m2oneb, <3>notboth, <3>m1case
      <4>m1te. m1 \in TranExclusive(oneb)  BY <4>m1old
      <4>m1tr. m1 \in Tran(oneb)  BY <4>m1te DEF TranExclusive
      <4>m1trm2. m1 \in Tran(m2)  BY <4>m1tr, <3>m2oneb
      <4> QED BY <4>m1trm2, <3>2
    <3>bothold. CASE m1 \in TranClosure(known \cup {p}) /\ m2 \in TranClosure(known \cup {p})
      <4>caught. a \in CaughtS(TranClosure(known \cup {p}))
        BY <3>2, <3>bothold DEF CaughtS
      <4> QED BY <4>caught, <2>anot
    <3>alldisj. m1 = oneb \/ m2 = oneb
                  \/ (m1 \in TranClosure(known \cup {p}) /\ m2 \in TranClosure(known \cup {p}))
      BY <3>m1case, <3>m2case
    <3> QED BY <3>alldisj, <3>m1oneb, <3>m2oneb, <3>bothold
  <2>eq. CaughtS(TranClosure(known \cup {p}) \cup {oneb}) = CaughtS(TranClosure(known \cup {p}))
    BY <1>mi, <1>tcKP, <2>anotoneb, CaughtSAddOne
  <2>comm. {oneb} \cup TranClosure(known \cup {p}) = TranClosure(known \cup {p}) \cup {oneb}  OBVIOUS
  <2> QED BY <2>ctran, <2>comm, <2>eq DEF Caught
<1>cbelow. CaughtS(TranClosure(m)) \subseteq CaughtS(TranClosure(known \cup {p}))
  <2> SUFFICES ASSUME NEW s \in CaughtS(TranClosure(m))
               PROVE s \in CaughtS(TranClosure(known \cup {p}))
    OBVIOUS
  <2>w1. s \in CaughtAcc(m)  BY DEF CaughtAcc
  <2>w2. CatchWitness1(m,s) \in CQ(m) /\ CatchWitness2(m,s) \in CQ(m)  BY <2>w1 DEF CQ
  <2>w3. CatchWitness1(m,s) \in TranClosure(CQ(m)) /\ CatchWitness2(m,s) \in TranClosure(CQ(m))
    BY <2>w2, TranClosureExpanding
  <2>w4. CatchWitness1(m,s) \in TranExclusive(p) /\ CatchWitness2(m,s) \in TranExclusive(p)
    BY <2>w3, <1>cqsubTEp
  <2>w5. /\ Sig(CatchWitness1(m,s)) = s /\ Sig(CatchWitness2(m,s)) = s
         /\ CatchWitness1(m,s) \notin Tran(CatchWitness2(m,s))
         /\ CatchWitness2(m,s) \notin Tran(CatchWitness1(m,s))
    BY <1>mi, <2>w1, CatchWitnessCorrect DEF CaughtAcc
  <2>w6. CatchWitness1(m,s) \in TranClosure(known \cup {p})
         /\ CatchWitness2(m,s) \in TranClosure(known \cup {p})
    BY <2>w4, <1>tepsub2
  <2> QED BY <2>w5, <2>w6 DEF CaughtS
<1>Scon. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))
  <2>cd. Con(alpha, oneb) = ConFromCaught(alpha, Caught(oneb))  BY DEF Con
  <2>ub. ConFromCaught(alpha, Caught(oneb)) \subseteq ConFromCaught(alpha, CaughtS(TranClosure(m)))
    <3>1. CaughtS(TranClosure(m)) \subseteq Caught(oneb)  BY <1>cbelow, <1>caughteq
    <3> QED BY <3>1, CFCAntitoneR
  <2>lb. ConFromCaught(alpha, CS2) \subseteq ConFromCaught(alpha, Caught(oneb))
    <3>1. Caught(oneb) \subseteq CS2  BY <1>caughteq
    <3> QED BY <3>1, CFCAntitoneR
  <2>eqhyp. ConFromCaught(alpha, CS2) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  OBVIOUS
  <2>s1. ConFromCaught(alpha, CaughtS(TranClosure(m))) \subseteq ConFromCaught(alpha, Caught(oneb))
    BY <2>lb, <2>eqhyp
  <2>s2. ConFromCaught(alpha, Caught(oneb)) = ConFromCaught(alpha, CaughtS(TranClosure(m)))
    BY <2>ub, <2>s1
  <2> QED BY <2>cd, <2>s2
<1> DEFINE S == ConFromCaught(alpha, CaughtS(TranClosure(m)))
<1> DEFINE SS == S \cap RelevantLearners(m)
<1>fresh. Fresh(alpha, oneb)
  <2>Vonebp. V(oneb) = V(p)  BY <1>Boneb, <1>bpbtarg DEF V
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
    <3>Voneb. V(oneb) = V(TopLearnerMsg(m,bs))  BY <2>Vonebp, <3>vp2
    <3>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>Scon
    <3>bsIn. bs \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>bsSraw2
    <3>xbetastarInCQ. TopLearnerMsg(m,bs) \in CQ(m)
      <4>rel. bs \in RelevantLearners(m)  BY <3>bsRel2
      <4> QED BY <4>rel DEF CQ
    <3>xbetastarInTEp. TopLearnerMsg(m,bs) \in TranExclusive(p)
      BY <3>xbetastarInCQ, TranClosureExpanding, <1>cqsubTEp
    <3>xbetastarInOneb. TopLearnerMsg(m,bs) \in TranExclusive(oneb)
      BY <3>xbetastarInTEp, <1>tepsub2
    <3> SUFFICES ASSUME NEW x \in Tran(oneb)
                 PROVE \/ V(x) = V(oneb)
                       \/ Con(alpha, oneb) \cap Lrns(x) = {}
                       \/ \E q \in TranExclusive(oneb) : B(q) > B(x) /\ Con(alpha, oneb) \cap Lrns(q) # {}
      BY DEF Fresh
    <3>xcase. x = oneb \/ x \in TranClosure(known \cup {p})  BY <1>tranoneb
    <3>caseA. CASE x = oneb  BY <3>caseA
    <3>caseB. CASE x \in TranClosure(known \cup {p})
      <4>casep. CASE x = p  BY <4>casep, <2>Vonebp
      <4>casenp. CASE x # p
        <5>cl. \/ ((B(x) <= bal) /\ (x \in TranClosure(m)))
               \/ ((B(x) > bal) /\ (B(x) < B(p)) /\ (V(x) = V(p)))
          BY <3>caseB, <4>casenp
        <5>chigh. CASE (B(x) > bal) /\ (B(x) < B(p)) /\ (V(x) = V(p))
          BY <5>chigh, <2>Vonebp
        <5>clow. CASE (B(x) <= bal) /\ (x \in TranClosure(m))
          <6>xm. x \in TranClosure(m)  BY <5>clow
          <6>empty. CASE Con(alpha, oneb) \cap Lrns(x) = {}  BY <6>empty
          <6>nonempty. CASE Con(alpha, oneb) \cap Lrns(x) # {}
            <7> PICK beta \in Con(alpha, oneb) \cap Lrns(x) : TRUE  BY <6>nonempty
            <7>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>S
            <7>betaLrns. beta \in Lrns(x)  OBVIOUS
            <7>xb. TopLearnerMsg(m,beta) \in TranClosure(m)
                   /\ beta \in Lrns(TopLearnerMsg(m,beta))
                   /\ B(x) <= B(TopLearnerMsg(m,beta))
              <8>ex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <6>xm, <7>betaLrns
              <8> QED BY <8>ex, <6>xm, <7>betaLrns, <1>mi, <1>btargnat, <1>boundt, TopLearnerMsgCorrect
            <7>bxbeta. B(x) <= BXBeta(m,beta)  BY <7>xb DEF BXBeta
            <7>bxbetastar. BXBeta(m,beta) <= BXBeta(m,bs)
              <8>ex2. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <6>xm, <7>betaLrns
              <8> QED BY <3>bsMaxraw2, <7>betaS, <8>ex2
            <7>xmsg. x \in Messages  BY <6>xm, <1>mi, TranClosureClosed
            <7>bxnat. B(x) \in Ballots  BY <7>xmsg, <1>mi, BBallot
            <7>bxbmsg. TopLearnerMsg(m,beta) \in Messages  BY <7>xb, <1>mi, TranClosureClosed
            <7>bxbnat. BXBeta(m,beta) \in Ballots  BY <7>bxbmsg, <1>mi, BBallot DEF BXBeta
            <7>bxbsmsg. TopLearnerMsg(m,bs) \in TranClosure(m)  BY <3>xbmsgs2
            <7>bxbsmsg2. TopLearnerMsg(m,bs) \in Messages  BY <7>bxbsmsg, <1>mi, TranClosureClosed
            <7>bxbsnat. BXBeta(m,bs) \in Ballots  BY <7>bxbsmsg2, <1>mi, BBallot DEF BXBeta
            <7>ineq. B(x) <= BXBeta(m,bs)
              BY <7>bxbeta, <7>bxbetastar, <7>bxnat, <7>bxbnat, <7>bxbsnat DEF Ballots
            <7>caseTie. CASE B(x) = BXBeta(m,bs)
              <8>eq1. B(x) = B(TopLearnerMsg(m,bs))  BY <7>caseTie DEF BXBeta
              <8>samebal. V(x) = V(TopLearnerMsg(m,bs))  BY <8>eq1 DEF V
              <8> QED BY <8>samebal, <3>Voneb
            <7>caseStrict. CASE B(x) < BXBeta(m,bs)
              <8>bq. B(x) < B(TopLearnerMsg(m,bs))  BY <7>caseStrict DEF BXBeta
              <8>lrnsx. Con(alpha, oneb) \cap Lrns(TopLearnerMsg(m,bs)) # {}
                <9>1. bs \in Con(alpha, oneb)  BY <3>S, <3>bsIn
                <9>2. bs \in Lrns(TopLearnerMsg(m,bs))  BY <3>bsLrns2
                <9> QED BY <9>1, <9>2
              <8> QED BY <3>xbetastarInOneb, <8>bq, <8>lrnsx
            <7> QED BY <7>ineq, <7>caseTie, <7>caseStrict
          <6> QED BY <6>empty, <6>nonempty
        <5> QED BY <5>cl, <5>chigh, <5>clow
      <4> QED BY <4>casep, <4>casenp
    <3> QED BY <3>xcase, <3>caseA, <3>caseB
  <2>caseE. CASE SS = {}
    <3>capempty. S \cap RelevantLearners(m) = {}  BY <2>caseE
    <3>capemptyraw. ConFromCaught(alpha, CaughtS(TranClosure(m))) \cap RelevantLearners(m) = {}
      BY <3>capempty
    <3>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>Scon
    <3> SUFFICES ASSUME NEW x \in Tran(oneb)
                 PROVE \/ V(x) = V(oneb)
                       \/ Con(alpha, oneb) \cap Lrns(x) = {}
                       \/ \E q \in TranExclusive(oneb) : B(q) > B(x) /\ Con(alpha, oneb) \cap Lrns(q) # {}
      BY DEF Fresh
    <3>xcase. x = oneb \/ x \in TranClosure(known \cup {p})  BY <1>tranoneb
    <3>caseA. CASE x = oneb  BY <3>caseA
    <3>caseB. CASE x \in TranClosure(known \cup {p})
      <4>casep. CASE x = p  BY <4>casep, <2>Vonebp
      <4>casenp. CASE x # p
        <5>cl. \/ ((B(x) <= bal) /\ (x \in TranClosure(m)))
               \/ ((B(x) > bal) /\ (B(x) < B(p)) /\ (V(x) = V(p)))
          BY <3>caseB, <4>casenp
        <5>chigh. CASE (B(x) > bal) /\ (B(x) < B(p)) /\ (V(x) = V(p))
          BY <5>chigh, <2>Vonebp
        <5>clow. CASE (B(x) <= bal) /\ (x \in TranClosure(m))
          <6>xm. x \in TranClosure(m)  BY <5>clow
          <6>empty. Con(alpha, oneb) \cap Lrns(x) = {}
            <7> SUFFICES ASSUME NEW beta \in Con(alpha, oneb) \cap Lrns(x) PROVE FALSE  OBVIOUS
            <7>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <3>S
            <7>betaLearner. beta \in Learners  BY DEF Lrns
            <7>betaex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <6>xm
            <7>betaRel. beta \in RelevantLearners(m)  BY <7>betaLearner, <7>betaex DEF RelevantLearners
            <7> QED BY <7>betaS, <7>betaRel, <3>capemptyraw
          <6> QED BY <6>empty
        <5> QED BY <5>cl, <5>chigh, <5>clow
      <4> QED BY <4>casep, <4>casenp
    <3> QED BY <3>xcase, <3>caseA, <3>caseB
  <2> QED BY <2>caseNE, <2>caseE
<1> QED BY <1>Boneb, <1>isoneb, <1>fresh
====================================================================
