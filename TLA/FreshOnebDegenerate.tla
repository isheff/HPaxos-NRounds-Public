------------------------ MODULE FreshOnebDegenerate ------------------------
EXTENDS MessageInterface,
        CQSubTC, TranClosureClosed, TranClosureAbsorb,
        TranClosureIdempotent, TranClosureUnion, TranClosureSingleton

\* Degenerate case: nobody relevant to alpha attests anything in TranClosure(m)
\* at all, so clause (b) resolves every ancestor other than oneb/p (which get
\* clause (a) directly, since V(p)=V(oneb) by construction).
LEMMA FreshOnebDegenerate ==
  ASSUME MessageInterfaceAssumptions,
         NEW m \in SUBSET Messages, NEW alpha \in Learners, NEW bal \in Ballots,
         NEW p, NEW btarg \in Ballots, NEW a \in Acceptors, NEW known \in SUBSET TranClosure(m),
         NEW oneb,
         p \in Proposals, TranExclusive(p) = TranClosure(CQ(m)), B(p) = btarg, Sig(p) \notin Acceptors,
         \A x \in TranClosure(m) : B(x) < bal, bal < btarg,
         oneb \in Messages, Sig(oneb) = a, IsOneB(oneb),
         TranExclusive(oneb) = TranClosure(known \cup {p}),
         B(oneb) = btarg,
         Caught(oneb) = CaughtS(TranClosure(m)),
         ConFromCaught(alpha, CaughtS(TranClosure(m))) \cap RelevantLearners(m) = {}
  PROVE Fresh(alpha, oneb)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
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
<1>Vonebp. V(oneb) = V(p)  BY DEF V
<1>tranoneb. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY DEF TranExclusive, Tran
<1>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY DEF Con
<1> SUFFICES ASSUME NEW x \in Tran(oneb)
             PROVE \/ V(x) = V(oneb)
                   \/ Con(alpha, oneb) \cap Lrns(x) = {}
                   \/ \E q \in TranExclusive(oneb) : B(q) > B(x) /\ Con(alpha, oneb) \cap Lrns(q) # {}
  BY DEF Fresh
<1>xcase. x = oneb \/ x \in TranClosure(known \cup {p})  BY <1>tranoneb
<1>caseA. CASE x = oneb  BY <1>caseA
<1>caseB. CASE x \in TranClosure(known \cup {p})
  <2>xcase2. x = p \/ x \in TranClosure(known \cup TranExclusive(p))  BY <1>caseB, <1>tc3
  <2>caseBp. CASE x = p  BY <2>caseBp, <1>Vonebp
  <2>caseBo. CASE x \in TranClosure(known \cup TranExclusive(p))
    <3>xm. x \in TranClosure(m)  BY <2>caseBo, <1>tc1, <1>knownsub, <1>tepsub
    <3>empty. Con(alpha, oneb) \cap Lrns(x) = {}
      <4> SUFFICES ASSUME NEW beta \in Con(alpha, oneb) \cap Lrns(x) PROVE FALSE  OBVIOUS
      <4>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>S
      <4>betaLearner. beta \in Learners  BY DEF Lrns
      <4>betaex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <3>xm
      <4>betaRel. beta \in RelevantLearners(m)  BY <4>betaLearner, <4>betaex DEF RelevantLearners
      <4> QED BY <4>betaS, <4>betaRel
    <3> QED BY <3>empty
  <2> QED BY <2>xcase2, <2>caseBp, <2>caseBo
<1> QED BY <1>xcase, <1>caseA, <1>caseB
====================================================================
