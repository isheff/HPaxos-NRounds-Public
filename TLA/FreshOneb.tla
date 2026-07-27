----------------------------- MODULE FreshOneb -----------------------------
EXTENDS MessageInterface,
        CQSubTC, TranClosureClosed, TranClosureAbsorb, TranClosureIdempotent,
        TranClosureUnion, TranClosureSingleton, TranClosureExpanding,
        TopLearnerMsgCorrect, BBallot

LEMMA FreshOneb ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW alpha \in Learners, NEW bal \in Ballots,
         NEW p, NEW btarg \in Ballots, NEW a \in Acceptors, NEW known \in SUBSET TranClosure(m),
         NEW oneb, NEW betastar \in Learners,
         p \in Proposals, TranExclusive(p) = TranClosure(CQ(m)), B(p) = btarg, Sig(p) \notin Acceptors,
         \A x \in TranClosure(m) : B(x) < bal, bal < btarg,
         oneb \in Messages, Sig(oneb) = a, IsOneB(oneb),
         TranExclusive(oneb) = TranClosure(known \cup {p}),
         B(oneb) = btarg,
         Caught(oneb) = CaughtS(TranClosure(m)),
         betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m))),
         TopLearnerMsg(m,betastar) \in TranClosure(m),
         betastar \in Lrns(TopLearnerMsg(m,betastar)),
         \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
           (\E x \in TranClosure(m) : beta \in Lrns(x)) =>
           BXBeta(m,beta) <= BXBeta(m,betastar),
         V(p) = V(TopLearnerMsg(m,betastar))
  PROVE Fresh(alpha, oneb)
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>bsmax. \A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
            (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar)
  OBVIOUS
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
<1>Vonebp. V(oneb) = V(p)  BY DEF V
<1>Vp. V(p) = V(TopLearnerMsg(m,betastar))  OBVIOUS
<1>Voneb. V(oneb) = V(TopLearnerMsg(m,betastar))  BY <1>Vonebp, <1>Vp
<1>tranoneb. Tran(oneb) = {oneb} \cup TranClosure(known \cup {p})  BY DEF TranExclusive, Tran
<1>S. Con(alpha, oneb) = ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY DEF Con
<1>bsIn. betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  OBVIOUS
<1>xbetastarInCQ. TopLearnerMsg(m,betastar) \in CQ(m)
  <2>rel. betastar \in RelevantLearners(m)
    <3>1. \E x \in TranClosure(m) : betastar \in Lrns(x)
      <4> WITNESS TopLearnerMsg(m,betastar) \in TranClosure(m)
      <4> QED OBVIOUS
    <3> QED BY <3>1 DEF RelevantLearners
  <2> QED BY <2>rel DEF CQ
<1>xbetastarInTEp. TopLearnerMsg(m,betastar) \in TranExclusive(p)
  BY <1>xbetastarInCQ, TranClosureExpanding, <1>tepeq
<1>xbetastarInKTEp. TopLearnerMsg(m,betastar) \in TranClosure(known \cup TranExclusive(p))
  BY <1>xbetastarInTEp, TranClosureExpanding
<1>xbetastarInOneb. TopLearnerMsg(m,betastar) \in TranExclusive(oneb)
  BY <1>xbetastarInKTEp, <1>tc3
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
    <3>xbal. B(x) < bal  BY <2>caseBo, <1>oldballs
    <3>empty. CASE Con(alpha, oneb) \cap Lrns(x) = {}  BY <3>empty
    <3>nonempty. CASE Con(alpha, oneb) \cap Lrns(x) # {}
      <4> PICK beta \in Con(alpha, oneb) \cap Lrns(x) : TRUE  BY <3>nonempty
      <4>betaS. beta \in ConFromCaught(alpha, CaughtS(TranClosure(m)))  BY <1>S
      <4>betaLrns. beta \in Lrns(x)  OBVIOUS
      <4>xb. TopLearnerMsg(m,beta) \in TranClosure(m)
             /\ beta \in Lrns(TopLearnerMsg(m,beta))
             /\ B(x) <= B(TopLearnerMsg(m,beta))
        <5>ex. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <3>xm, <4>betaLrns
        <5> QED BY <5>ex, <3>xm, <4>betaLrns, <1>mi, <1>balnat, <1>bound, TopLearnerMsgCorrect
      <4>bxbeta. B(x) <= BXBeta(m,beta)  BY <4>xb DEF BXBeta
      <4>bxbetastar. BXBeta(m,beta) <= BXBeta(m,betastar)
        <5>ex2. \E y \in TranClosure(m) : beta \in Lrns(y)  BY <3>xm, <4>betaLrns
        <5> QED BY <1>bsmax, <4>betaS, <5>ex2
      <4>xmsg. x \in Messages  BY <3>xm, <1>mi, TranClosureClosed
      <4>bxnat. B(x) \in Ballots  BY <4>xmsg, <1>mi, BBallot
      <4>bxbmsg. TopLearnerMsg(m,beta) \in Messages  BY <4>xb, <1>mi, TranClosureClosed
      <4>bxbnat. BXBeta(m,beta) \in Ballots  BY <4>bxbmsg, <1>mi, BBallot DEF BXBeta
      <4>bxbsmsg. TopLearnerMsg(m,betastar) \in TranClosure(m)  OBVIOUS
      <4>bxbsmsg2. TopLearnerMsg(m,betastar) \in Messages  BY <4>bxbsmsg, <1>mi, TranClosureClosed
      <4>bxbsnat. BXBeta(m,betastar) \in Ballots  BY <4>bxbsmsg2, <1>mi, BBallot DEF BXBeta
      <4>ineq. B(x) <= BXBeta(m,betastar)
        BY <4>bxbeta, <4>bxbetastar, <4>bxnat, <4>bxbnat, <4>bxbsnat DEF Ballots
      <4>caseTie. CASE B(x) = BXBeta(m,betastar)
        <5>eq1. B(x) = B(TopLearnerMsg(m,betastar))  BY <4>caseTie DEF BXBeta
        <5>samebal. V(x) = V(TopLearnerMsg(m,betastar))  BY <5>eq1 DEF V
        <5> QED BY <5>samebal, <1>Voneb
      <4>caseStrict. CASE B(x) < BXBeta(m,betastar)
        <5>bq. B(x) < B(TopLearnerMsg(m,betastar))  BY <4>caseStrict DEF BXBeta
        <5>lrnsx. Con(alpha, oneb) \cap Lrns(TopLearnerMsg(m,betastar)) # {}
          <6>1. betastar \in Con(alpha, oneb)  BY <1>S, <1>bsIn
          <6>2. betastar \in Lrns(TopLearnerMsg(m,betastar))  OBVIOUS
          <6> QED BY <6>1, <6>2
        <5> QED BY <1>xbetastarInOneb, <5>bq, <5>lrnsx
      <4> QED BY <4>ineq, <4>caseTie, <4>caseStrict
    <3> QED BY <3>empty, <3>nonempty
  <2> QED BY <2>xcase2, <2>caseBp, <2>caseBo
<1> QED BY <1>xcase, <1>caseA, <1>caseB
====================================================================
