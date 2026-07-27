----------------------------- MODULE OneBFresh -----------------------------
EXTENDS MessageInterface, OneBExists, FreshOneb

\* Lean wrapper: bundles OneBExists+FreshOneb behind a small clean-context
\* ASSUME so citing them from the (much heavier) DecideableProposalExists
\* context doesn't exhaust the backend's search. The bal/btarg/betastar
\* parameters are bundled into an \E premise because they do not appear in
\* the conclusion.
LEMMA OneBFresh ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW alpha \in Learners, NEW p \in Proposals,
         \E bal \in Ballots, btarg \in Ballots, betastar \in Learners :
           /\ TranExclusive(p) = TranClosure(CQ(m))
           /\ B(p) = btarg
           /\ Sig(p) \notin Acceptors
           /\ (\A x \in TranClosure(m) : B(x) < bal)
           /\ bal < btarg
           /\ betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
           /\ TopLearnerMsg(m,betastar) \in TranClosure(m)
           /\ betastar \in Lrns(TopLearnerMsg(m,betastar))
           /\ (\A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
                (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar))
           /\ V(p) = V(TopLearnerMsg(m,betastar))
  PROVE \A a \in Acceptors :
          \A known \in SUBSET TranClosure(m) :
            (/\ IsFiniteSet(known) /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p))))
            => \E oneb \in Messages :
                 (/\ Sig(oneb) = a /\ a \notin Caught(oneb) /\ IsOneB(oneb)
                  /\ TranExclusive(oneb) = TranClosure(known \cup {p}) /\ Fresh(alpha, oneb))
<1> PICK bal \in Ballots, btarg \in Ballots, betastar \in Learners :
      /\ TranExclusive(p) = TranClosure(CQ(m))
      /\ B(p) = btarg
      /\ Sig(p) \notin Acceptors
      /\ (\A x \in TranClosure(m) : B(x) < bal)
      /\ bal < btarg
      /\ betastar \in ConFromCaught(alpha, CaughtS(TranClosure(m)))
      /\ TopLearnerMsg(m,betastar) \in TranClosure(m)
      /\ betastar \in Lrns(TopLearnerMsg(m,betastar))
      /\ (\A beta \in ConFromCaught(alpha, CaughtS(TranClosure(m))) :
           (\E x \in TranClosure(m) : beta \in Lrns(x)) => BXBeta(m,beta) <= BXBeta(m,betastar))
      /\ V(p) = V(TopLearnerMsg(m,betastar))
  OBVIOUS
<1> SUFFICES ASSUME NEW a \in Acceptors, NEW known \in SUBSET TranClosure(m),
                    IsFiniteSet(known), a \notin CaughtS(TranClosure(known \cup TranExclusive(p)))
             PROVE \E oneb \in Messages :
                     (/\ Sig(oneb) = a /\ a \notin Caught(oneb) /\ IsOneB(oneb)
                      /\ TranExclusive(oneb) = TranClosure(known \cup {p}) /\ Fresh(alpha, oneb))
  OBVIOUS
<1>oex. \E oneb \in Messages :
          /\ Sig(oneb) = a
          /\ a \notin Caught(oneb)
          /\ IsOneB(oneb)
          /\ TranExclusive(oneb) = TranClosure(known \cup {p})
          /\ B(oneb) = btarg
          /\ Caught(oneb) = CaughtS(TranClosure(m))
  BY LearnerGraphAssumptions, OneBExists
<1> PICK oneb \in Messages :
      /\ Sig(oneb) = a
      /\ a \notin Caught(oneb)
      /\ IsOneB(oneb)
      /\ TranExclusive(oneb) = TranClosure(known \cup {p})
      /\ B(oneb) = btarg
      /\ Caught(oneb) = CaughtS(TranClosure(m))
  BY <1>oex
<1>fresh. Fresh(alpha, oneb)
  BY LearnerGraphAssumptions, FreshOneb
<1> QED BY <1>fresh
====================================================================
