-------------------------- MODULE AlwaysANewTwoAInstT --------------------------
EXTENDS HPaxosPlusCal

\* Isolated, freshly-named instantiation wrapper for AlwaysANewTwoA: avoids the
\* ambient "x" (the newly-learned message, in scope everywhere this gets used)
\* colliding with the axiom's own internally-bound "x", and keeps the
\* surrounding hypothesis context small enough for the backend to match.
LEMMA AlwaysANewTwoAInstT ==
  ASSUME MessageInterfaceAssumptions,
         NEW mm \in SUBSET Messages, NEW bb \in Ballots, NEW aa \in Acceptors,
         NEW alpha \in Learners, NEW dd \in (1..MaxDepth(alpha)),
         IsFiniteSet(mm), \A zz \in mm : B(zz) <= bb,
         aa \notin CaughtS(TranClosure(mm)),
         SigS({zz \in TranClosure(mm) : B(zz) = bb /\ HasDepth(alpha, zz, dd-1)}) \in Quorums(alpha)
  PROVE \E yy \in Messages :
          /\ (yy \in TranClosure(mm) \/ TranClosure(mm) = TranExclusive(yy))
          /\ B(yy) = bb
          /\ Sig(yy) = aa
          /\ HasDepth(alpha, yy, dd)
          /\ aa \notin Caught(yy)
          /\ IsTwoA(yy)
<1>ant. AlwaysANewTwoA  BY DEF MessageInterfaceAssumptions
<1> QED BY <1>ant DEF AlwaysANewTwoA
====================================================================
