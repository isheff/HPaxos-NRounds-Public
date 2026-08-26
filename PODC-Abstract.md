# Working title options

- **Asymmetry All the Way Up: Machine-Checked Heterogeneous Consensus from Learner Graphs and Authentication**
- Heterogeneous Consensus Is Real: Learner Graphs, Authentication, and a Machine-Checked Liveness Proof
- Escaping Symmetry: Verified Heterogeneous Consensus with Learner Graphs

# Abstract

Can consensus be genuinely heterogeneous, or does every protocol for
participants with differing failure assumptions secretly collapse into a
homogeneous one? A recent result (*Symmetry All the Way Down*, DISC 2026)
gives a sharp negative answer for asymmetric quorum systems without
authentication: every failure scenario in which asymmetric trust can solve
consensus can already be tolerated by a suitably constructed *symmetric*
quorum system, so heterogeneity buys new tolerance only for tasks strictly
weaker than consensus.

We show that this collapse is a property of that setting, not of
heterogeneity. Two ingredients suffice to escape it. First, the *learner
graph* separates the parties who decide (learners) from the parties who vote
(acceptors) and makes the specification itself subjective: each learner
states its own mixed crash/Byzantine assumptions, and each *pair* of learners
states the conditions under which they must agree. In a single execution,
learners whose mutual assumptions hold agree, while learners whose
assumptions fail may safely diverge — a guarantee profile no single symmetric
system offers. Second, *authentication*: signed messages carrying their
causal history let evidence cross trust domains, so equivocators are provably
caught rather than assumed away.

We present a repaired and generalized Heterogeneous Paxos, fixing a liveness
bug in the OPODIS 2020 protocol, together with — to our knowledge — the first
fully machine-checked safety *and* liveness proofs for a heterogeneous
consensus protocol: roughly 370 TLAPS modules, checked down to temporal
logic. Liveness holds under notably weak assumptions: the network owes
delivery only of messages a live acceptor has sent or learned, and every
hypothesis about the message history ranges only over messages live acceptors
ever learn — a Byzantine proposer may flood the network with competing
proposals without harm, so long as no live acceptor receives them. We further
prove accountability: any equivocation whose two witnesses reach live
acceptors is eventually detected by every live acceptor.

*(~300 words)*

## Framing notes (not part of the abstract)

- The contrast is complementary, not contradictory: the DISC result is proved
  in the asynchronous **unauthenticated** setting for **asymmetric quorum
  systems**, where one global task must be solved by the same processes that
  hold the trust assumptions. Both escape hatches are named explicitly so
  reviewers see the boundary rather than a challenge to their theorem.
- "Roughly 370 TLAPS modules" — current count is 372; adjust at submission.
- The weak-liveness claims map to the formalization: `NetworkAssumption`
  restricted to live-relevant messages, `TranFairness(p)` for the designated
  proposal's history, `IsAllMessagesEverKnown` hypotheses, and the
  `EventuallyCaught` theorem.
- PODC 2026 accepted work on authentication-setting boundaries ("Byzantine
  Consensus in the Partially Authenticated Setting"), so the
  authentication-as-ingredient framing is topical.
