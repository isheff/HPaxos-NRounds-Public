-------------------- MODULE DecideableProposalOneBFreshRW --------------------
EXTENDS HPaxosPlusCal, DecideableProposalOneBFreshR

\* Thin wrapper for the relaxed freshness engine.
LEMMA DecideableProposalOneBFreshRW ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, ValueInterfaceAssumptions,
         NEW alpha \in Learners, NEW bal \in Ballots, NEW m \in SUBSET Messages,
         NEW p \in Proposals, NEW a \in Acceptors,
         NEW known \in SUBSET Messages, NEW oneb \in (Messages \ Proposals),
         NEW CS2,
         DPFreshHypR(alpha, bal, m, p, a, known, oneb, CS2)
  PROVE /\ B(oneb) = B(p)
        /\ IsOneB(oneb)
        /\ Fresh(alpha, oneb)
BY DecideableProposalOneBFreshR DEF DPFreshHypR
====================================================================
