------------------------ MODULE OneBFreshDegenerate ------------------------
EXTENDS MessageInterface, OneBExists, FreshOnebDegenerate

LEMMA OneBFreshDegenerate ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         NEW m \in SUBSET Messages, NEW alpha \in Learners, NEW p \in Proposals,
         \E bal \in Ballots, btarg \in Ballots :
           /\ TranExclusive(p) = TranClosure(CQ(m))
           /\ B(p) = btarg
           /\ Sig(p) \notin Acceptors
           /\ (\A x \in TranClosure(m) : B(x) < bal)
           /\ bal < btarg,
         ConFromCaught(alpha, CaughtS(TranClosure(m))) \cap RelevantLearners(m) = {}
  PROVE \A a \in Acceptors :
          \A known \in SUBSET TranClosure(m) :
            (/\ IsFiniteSet(known) /\ a \notin CaughtS(TranClosure(known \cup TranExclusive(p))))
            => \E oneb \in Messages :
                 (/\ Sig(oneb) = a /\ a \notin Caught(oneb) /\ IsOneB(oneb)
                  /\ TranExclusive(oneb) = TranClosure(known \cup {p}) /\ Fresh(alpha, oneb))
<1> PICK bal \in Ballots, btarg \in Ballots :
      /\ TranExclusive(p) = TranClosure(CQ(m))
      /\ B(p) = btarg
      /\ Sig(p) \notin Acceptors
      /\ (\A x \in TranClosure(m) : B(x) < bal)
      /\ bal < btarg
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
  BY FreshOnebDegenerate
<1> QED BY <1>fresh
====================================================================
