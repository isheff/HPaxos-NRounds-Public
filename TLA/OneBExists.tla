---------------------------- MODULE OneBExists ----------------------------
\* The widest citation set so far: the full TranClosure algebra, both CaughtS
\* bookkeeping lemmas, the CQ construction, and the ballot lemmas. All by
\* EXTENDS -- every one of them sits on MessageInterface, which this module
\* also needs, so LOCAL INSTANCE would fork the shared base.
EXTENDS MessageInterface, FiniteSetTheorems,
        CQFinite, CQSubTC,
        TranClosureClosed, TranClosureAbsorb, TranClosureIdempotent,
        TranClosureUnion, TranClosureSingleton, TranClosureExpanding,
        BBallot, CaughtSAddNonAcceptor, CaughtSAddOne,
        ProposalBalOfP, BOfAbsorbing, CatchWitnessCorrect

LEMMA OneBExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW bal \in Ballots,
         NEW p, NEW btarg \in Ballots,
         p \in Proposals, TranExclusive(p) = TranClosure(CQ(m)), B(p) = btarg, Sig(p) \notin Acceptors,
         \A x \in TranClosure(m) : B(x) < bal,
         bal < btarg,
         NEW a \in Acceptors, NEW known \in SUBSET TranClosure(m), IsFiniteSet(known),
         a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
  PROVE \E oneb \in Messages :
          /\ Sig(oneb) = a
          /\ a \notin Caught(oneb)
          /\ IsOneB(oneb)
          /\ TranExclusive(oneb) = TranClosure(known \cup {p})
          /\ B(oneb) = btarg
          /\ Caught(oneb) = CaughtS(TranClosure(m))
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal /\ AlwaysANewOneB
  BY DEF MessageInterfaceAssumptions
<1>anob. AlwaysANewOneB  BY DEF MessageInterfaceAssumptions
<1>cfin. IsFiniteSet(CQ(m))  BY LearnerGraphAssumptions, CQFinite
<1>balnat. bal \in Nat  BY DEF Ballots
<1>btnat. btarg \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
<1>tepeq. TranExclusive(p) = TranClosure(CQ(m))  OBVIOUS
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
<1>oldballs. \A x \in TranClosure(known \cup TranExclusive(p)) : B(x) < bal
  BY <1>tc1, <1>knownsub, <1>tepsub
<1>ktepmsgs. TranClosure(known \cup TranExclusive(p)) \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in TranClosure(known \cup TranExclusive(p)) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>tc1, <1>knownsub, <1>tepsub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>knownfin. IsFiniteSet(known \cup {p})  BY FS_Singleton, FS_Union
<1>bpbtarg. B(p) = btarg  OBVIOUS
<1>baltbarg2. bal < btarg  OBVIOUS
<1>ballsleb. \A x \in known \cup {p} : B(x) <= btarg
  <2> SUFFICES ASSUME NEW x \in known \cup {p} PROVE B(x) <= btarg  OBVIOUS
  <2>1. CASE x = p
    <3>bxp. B(x) = B(p)  BY <2>1
    <3> QED BY <3>bxp, <1>bpbtarg, <1>btnat
  <2>2. CASE x \in known
    <3>1. x \in TranClosure(m)  BY <2>2
    <3>2. B(x) < bal  BY <3>1, <1>bound
    <3>3. B(x) \in Ballots  BY <3>1, <1>mi, TranClosureClosed, BBallot
    <3> QED BY <3>2, <3>3, <1>baltbarg2, <1>balnat, <1>btnat DEF Ballots
  <2> QED BY <2>1, <2>2
<1>cardone. Cardinality({x \in TranClosure(known \cup {p}) : B(x) = btarg}) = 1
  <2>eq. {x \in TranClosure(known \cup {p}) : B(x) = btarg} = {p}
    <3> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), B(x) = btarg
                 PROVE x = p
      BY <1>tc3
    <3>1. x \in TranClosure(known \cup TranExclusive(p)) \/ x = p  BY <1>tc3
    <3>2. CASE x = p  BY <3>2
    <3>3. CASE x \in TranClosure(known \cup TranExclusive(p))
      <4>1. B(x) < bal  BY <3>3, <1>oldballs
      <4>2. x \in Messages  BY <3>3, <1>ktepmsgs
      <4>3. B(x) \in Ballots  BY <4>2, <1>mi, BBallot
      <4> QED BY <4>1, <4>3, <1>baltbarg2, <1>balnat, <1>btnat DEF Ballots
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>eq, FS_Singleton
<1>capp. a \notin CaughtS(TranClosure(known \cup {p}))
  <2>1. CaughtS(TranClosure(known \cup {p})) = CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
    BY <1>tc3
  <2>2. CaughtS(TranClosure(known \cup TranExclusive(p)) \cup {p})
          = CaughtS(TranClosure(known \cup TranExclusive(p)))
    BY <1>mi, <1>ktepmsgs, CaughtSAddNonAcceptor
  <2> QED BY <2>1, <2>2
<1>anexhyp. \E bb \in Ballots :
             /\ IsFiniteSet(known \cup {p})
             /\ (\A x \in known \cup {p} : B(x) <= bb)
             /\ Cardinality({x \in TranClosure(known \cup {p}) : B(x) = bb}) = 1
             /\ a \notin CaughtS(TranClosure(known \cup {p}))
  <2> WITNESS btarg \in Ballots
  <2> QED BY <1>knownfin, <1>ballsleb, <1>cardone, <1>capp, <1>btnat
<1>anb. \E oneb \in Messages :
          /\ Sig(oneb) = a
          /\ a \notin Caught(oneb)
          /\ IsOneB(oneb)
          /\ TranExclusive(oneb) = TranClosure(known \cup {p})
  <2> PICK bb \in Ballots :
        /\ IsFiniteSet(known \cup {p})
        /\ (\A x \in known \cup {p} : B(x) <= bb)
        /\ Cardinality({x \in TranClosure(known \cup {p}) : B(x) = bb}) = 1
        /\ a \notin CaughtS(TranClosure(known \cup {p}))
    BY <1>anexhyp
  <2>kpm. known \cup {p} \in SUBSET Messages
    <3> SUFFICES ASSUME NEW z \in known \cup {p} PROVE z \in Messages  OBVIOUS
    <3>1. CASE z \in known  BY <3>1, <1>knownmsgs
    <3>2. CASE z = p  BY <3>2, <1>mi DEF TypeOKMessageInterface
    <3> QED BY <3>1, <3>2
  <2> PICK KP \in SUBSET Messages :
        /\ KP = known \cup {p}
        /\ IsFiniteSet(KP)
        /\ (\A x \in KP : B(x) <= bb)
        /\ Cardinality({x \in TranClosure(KP) : B(x) = bb}) = 1
        /\ a \notin CaughtS(TranClosure(KP))
    <3> WITNESS known \cup {p} \in SUBSET Messages
    <3> QED BY <2>kpm
  <2>ax. \E oneb \in Messages :
           /\ Sig(oneb) = a
           /\ a \notin Caught(oneb)
           /\ IsOneB(oneb)
           /\ TranExclusive(oneb) = TranClosure(KP)
    BY <1>anob DEF AlwaysANewOneB
  <2> QED BY <2>ax
<1> PICK oneb \in Messages :
      /\ Sig(oneb) = a
      /\ a \notin Caught(oneb)
      /\ IsOneB(oneb)
      /\ TranExclusive(oneb) = TranClosure(known \cup {p})
  BY <1>anb
<1>onebnotprop. oneb \notin Proposals  BY DEF IsOneB, IsProposal
<1>cqoldballs. \A x \in TranClosure(CQ(m)) : B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(CQ(m)) PROVE B(x) < btarg  OBVIOUS
  <2>1. x \in TranClosure(m)  BY <1>csub, <1>mi, <1>cqmsgs, TranClosureAbsorb
  <2>2. B(x) < bal  BY <2>1, <1>bound
  <2>3. B(x) \in Ballots  BY <2>1, <1>mi, TranClosureClosed, BBallot
  <2> QED BY <2>2, <2>3, <1>baltbarg2, <1>balnat, <1>btnat DEF Ballots
<1>pbalp. ProposalBal(p) = btarg
  BY <1>tepeq, <1>cqmsgs, <1>bpbtarg, <1>cqoldballs, ProposalBalOfP
<1>notpballs. \A x \in TranClosure(known \cup {p}) : x # p => B(x) < btarg
  <2> SUFFICES ASSUME NEW x \in TranClosure(known \cup {p}), x # p PROVE B(x) < btarg  OBVIOUS
  <2>1. x \in TranClosure(known \cup TranExclusive(p))  BY <1>tc3
  <2>2. B(x) < bal  BY <2>1, <1>oldballs
  <2>3. x \in Messages  BY <2>1, <1>ktepmsgs
  <2>4. B(x) \in Ballots  BY <2>3, <1>mi, BBallot
  <2> QED BY <2>2, <2>4, <1>baltbarg2, <1>balnat, <1>btnat DEF Ballots
<1>pinS. p \in TranClosure(known \cup {p})
  <2>1. p \in Tran(p)  BY DEF Tran
  <2> QED BY <2>1 DEF TranClosure
<1>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>kpmsgs. TranClosure(known \cup {p}) \subseteq Messages  BY <1>tc3, <1>ktepmsgs, <1>pmsg
<1>onebmsg. oneb \in Messages  OBVIOUS
<1>Boneb. B(oneb) = btarg
  BY <1>mi, <1>onebmsg, <1>kpmsgs, BOfAbsorbing, <1>onebnotprop, <1>pbalp, <1>notpballs, <1>pinS
<1>caughtoneb. Caught(oneb) = CaughtS(TranClosure(m))
  <2>ctran. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY DEF TranExclusive, Tran
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
    <3>anot. a \notin CaughtS(TranClosure(known \cup {p}))  BY <1>capp
    <3>anotoneb. a \notin CaughtS(TranClosure(known \cup {p}) \cup {oneb})
      <4>1. CaughtS(TranClosure(known \cup {p}) \cup {oneb}) = Caught(oneb)  BY <3>comm, <2>ctran DEF Caught
      <4> QED BY <4>1
    <3>eq. CaughtS(TranClosure(known \cup {p}) \cup {oneb}) = CaughtS(TranClosure(known \cup {p}))
      BY <1>mi, <1>kpmsgs, <3>anot, <3>anotoneb, CaughtSAddOne
    <3> QED BY <3>comm, <3>eq
  <2> QED BY <2>ctran, <2>step1, <2>step2, <2>step3 DEF Caught
<1> QED BY <1>Boneb, <1>caughtoneb
====================================================================
