------------------------------ MODULE PExists ------------------------------
EXTENDS MessageInterface, CQFinite, CQSubTC, TranClosureClosed, BBallot

\* Constructing p: a fresh proposal above every ballot in the closure,
\* carrying the target value, whose strict closure is exactly TranClosure(CQ(m)).
LEMMA PExists ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW m \in SUBSET Messages, NEW bal \in Ballots, NEW targetVal \in Values,
         \A x \in TranClosure(m) : B(x) < bal
  PROVE \E p \in Proposals :
          /\ TranExclusive(p) = TranClosure(CQ(m))
          /\ B(p) > bal
          /\ Sig(p) \notin Acceptors
          /\ V(p) = targetVal
<1>mi. TypeOKMessageInterface /\ TranTrans /\ TranFinite /\ AlwaysAProposal /\ AlwaysANewProposal
  BY DEF MessageInterfaceAssumptions
<1>lga. LearnerGraphAssumptions  OBVIOUS
<1>via. AlwaysAHigherBallot  BY DEF ValueInterfaceAssumptions
<1>cfin. IsFiniteSet(CQ(m))  BY <1>lga, CQFinite
<1>balnat. bal \in Nat  BY DEF Ballots
<1>bound. \A x \in TranClosure(m) : B(x) < bal  OBVIOUS
<1>csub. CQ(m) \subseteq TranClosure(m)  BY <1>mi, <1>balnat, <1>bound, CQSubTC
<1>hb. \E b \in Ballots : bal < b /\ BalToVal(b) = targetVal  BY <1>via DEF AlwaysAHigherBallot
<1> PICK b \in Ballots : bal < b /\ BalToVal(b) = targetVal  BY <1>hb
<1>bnat. b \in Nat  BY DEF Ballots
<1>cballs. \A x \in CQ(m) : B(x) < b
  <2> SUFFICES ASSUME NEW x \in CQ(m) PROVE B(x) < b  OBVIOUS
  <2>1. x \in TranClosure(m)  BY <1>csub
  <2>1m. x \in Messages  BY <2>1, <1>mi, TranClosureClosed
  <2>2. B(x) < bal  BY <2>1, <1>bound
  <2>3. B(x) \in Ballots  BY <2>1m, <1>mi, BBallot
  <2>4. B(x) \in Nat  BY <2>3 DEF Ballots
  <2> QED BY <2>2, <2>4, <1>balnat, <1>bnat
<1>cqmsgs. CQ(m) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW z \in CQ(m) PROVE z \in Messages  OBVIOUS
  <2>1. z \in TranClosure(m)  BY <1>csub
  <2> QED BY <2>1, <1>mi, TranClosureClosed
<1>anp. \E p \in Proposals :
          /\ TranExclusive(p) = TranClosure(CQ(m))
          /\ B(p) = b
          /\ Sig(p) \notin Acceptors
  BY <1>mi, <1>cqmsgs, <1>cfin, <1>cballs DEF AlwaysANewProposal
<1> PICK p \in Proposals :
      /\ TranExclusive(p) = TranClosure(CQ(m))
      /\ B(p) = b
      /\ Sig(p) \notin Acceptors
  BY <1>anp
<1>vp. V(p) = targetVal  BY DEF V
<1> QED BY <1>vp
====================================================================
