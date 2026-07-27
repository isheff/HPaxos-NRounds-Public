----------------------- MODULE TopLearnerMsgCorrect -----------------------
EXTENDS MessageInterface, FiniteSetTheorems,
        TranClosureClosed, BBallot, NatMaxExists

LEMMA TopLearnerMsgCorrect ==
  ASSUME TypeOKMessageInterface, TranTrans, TranFinite, AlwaysAProposal,
         NEW mm \in SUBSET Messages, NEW bd \in Nat, NEW beta,
         \A x \in TranClosure(mm) : B(x) < bd,
         \E x \in TranClosure(mm) : beta \in Lrns(x)
  PROVE /\ TopLearnerMsg(mm, beta) \in TranClosure(mm)
        /\ beta \in Lrns(TopLearnerMsg(mm, beta))
        /\ \A y \in TranClosure(mm) : beta \in Lrns(y) => B(y) <= B(TopLearnerMsg(mm, beta))
<1> DEFINE Cand == {x \in TranClosure(mm) : beta \in Lrns(x)}
<1> DEFINE Bals == {B(x) : x \in Cand}
<1>ne. Cand # {}  OBVIOUS
<1>candmsg. Cand \subseteq Messages
  <2> SUFFICES ASSUME NEW z \in Cand PROVE z \in Messages  OBVIOUS
  <2>0. z \in TranClosure(mm)  OBVIOUS
  <2> QED BY <2>0, TranClosureClosed
<1>balssub. Bals \subseteq 0..bd
  <2> SUFFICES ASSUME NEW w \in Bals PROVE w \in 0..bd  OBVIOUS
  <2>1. PICK z \in Cand : w = B(z)  OBVIOUS
  <2>2. z \in TranClosure(mm)  BY <2>1
  <2>3. B(z) \in Ballots  BY <2>1, <1>candmsg, BBallot
  <2>4. B(z) \in Nat  BY <2>3 DEF Ballots
  <2>5. B(z) < bd  BY <2>2
  <2> QED BY <2>1, <2>4, <2>5
<1>balsfin. IsFiniteSet(Bals)
  <2>1. IsFiniteSet(0..bd)  BY FS_Interval
  <2> QED BY <2>1, <1>balssub, FS_Subset
<1>balsne. Bals # {}  BY <1>ne
<1>balssubnat. Bals \subseteq Nat  BY <1>balssub
<1>maxex. \E r \in Bals : \A y \in Bals : y <= r
  BY <1>balsfin, <1>balsne, <1>balssubnat, NatMaxExists
<1> PICK hibal \in Bals : \A y \in Bals : y <= hibal  BY <1>maxex
<1> PICK x \in Cand : B(x) = hibal  OBVIOUS
<1>xTC. x \in TranClosure(mm) /\ beta \in Lrns(x)  OBVIOUS
<1>xmax. \A y \in TranClosure(mm) : beta \in Lrns(y) => B(y) <= B(x)
  <2> SUFFICES ASSUME NEW y \in TranClosure(mm), beta \in Lrns(y) PROVE B(y) <= B(x)  OBVIOUS
  <2>1. y \in Cand  OBVIOUS
  <2>2. B(y) \in Bals  BY <2>1
  <2> QED BY <2>2
<1> QED BY <1>xTC, <1>xmax DEF TopLearnerMsg
====================================================================
