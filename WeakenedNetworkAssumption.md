# Weakening NetworkAssumption to live-relevant messages

**Question.** Weaken `NetworkAssumption` in `HPaxosPlusCal` so fairness applies
only to messages *sent by* (`Sig`) or *known to* (`known_messages`) a
`LiveAcceptor`. Can we still prove all the theorems?

**Answer.** Yes — every theorem is re-proved (all obligations, tlapm
`1.6.0-pre`), with two necessary statement adjustments:

1. The eventual-knowledge results (`KnowLeadsTo`, `LearnLeadsTo`,
   `EventuallyKnown`, `EventuallyKnownInvariant`) now have leads-to *sources*
   restricted to live-relevant messages.
2. The termination chain (`TerminatingProposal*`, `Termination`) takes one new
   hypothesis, `TranFairness(p)`: receipt of the designated proposal p and of
   everything in its transitive history is (unconditionally) weakly fair.

All safety theorems are untouched — none of them mention `NetworkAssumption`.

## The weakened definition

```tla
LiveRelevant(x) ==
  \/ Sig(x) \in LiveAcceptors
  \/ \E b \in LiveAcceptors : x \in known_messages[b]

relevant_receive(self) ==
  safe_acceptor_receives_message(self) /\ LiveRelevant(self[2])

NetworkAssumption ==
  \A self \in LiveAcceptors \times Messages : WF_vars(relevant_receive(self))
```

WF of the *restricted* action: fairness is owed only while the message is
currently live-relevant. `LiveRelevant` is monotone under `Spec`
(known_messages only grows, Sig is constant), so this is equivalent under
`Spec` to the conditional form `<>LiveRelevant(self[2]) => WF_vars(receive)`.
The concrete side (`CNetworkAssumption` over `CRelevantStep`) is weakened
identically, and `CLivenessTransfer` still gives
`CSpec /\ CNetworkAssumption => Spec /\ NetworkAssumption`.

## Why the unweakened statements become FALSE (not merely unprovable)

`LiveRelevant` bootstraps for live-signed messages but never for the *first
receipt* of a Byzantine-signed one. Countermodel: a Byzantine sender (e.g. a
proposer — `Sig(p) \notin Acceptors`) sends p, then the system stutters
forever. No live acceptor signed p and none knows it, so
`relevant_receive((a,p))` is never enabled and every WF conjunct is vacuously
satisfied; `Spec /\ NetworkAssumption` holds, yet p is never learned and no
decision is ever reached. Hence the old `EventuallyKnown`
(`m \subseteq Msgs ~> ...`) and the old `Termination` (with only
`<>(p \in Msgs)` as trigger) are false under the weakening. WF on the pair
`(a, p)` *alone* would not fix termination either: receiving p is enabled only
once `TranExclusive(p) \subseteq known_messages[a]`, and nothing forces the
history (in general Byzantine-signed catch witnesses / top-learner messages)
to be learned — so the fairness assumption must cover p's history bottom-up.

## What makes the weakened chain work

`RelevantMsgs == {x \in Msgs : LiveRelevant(x)}` is (a) monotone and (b)
closed under `TranExclusive` at reachable states (`BoxRelTranClosed`, from the
established invariants: a known message's history is known —
`KnownTranClosureInvT` — and a live-signed message's history is bounded by its
signer's knowledge plus its own signed messages — `SelfSentBoundedInvT`). So
the Tran-depth induction of `KnowLeadsTo` goes through verbatim with sources
`\in / \subseteq RelevantMsgs`, and `EventuallyKnown` becomes:

```
(m \subseteq RelevantMsgs) ~> (\A a \in LiveAcceptors : m \subseteq known_messages[a])
```

The 2A cascade needs no further assumptions: the depth-d witness sets
(`WPrimeStep`) are live-SIGNED, hence in `RelevantMsgs` whenever on the
network (bridge inside `TwoAStepLtProduceR`; `TwoAStepLtOp`'s statement is
unchanged).

## The termination hypothesis

```tla
TranFairness(pp) ==
  \A self \in LiveAcceptors \times Tran(pp) :
    WF_vars(safe_acceptor_receives_message(self))
```

Because `Tran` is transitively closed (`TranTrans`), unconditional WF over
`LiveAcceptors \X Tran(p)` supports the original (unweakened) induction
restricted to `Tran(p)` — `KnowLeadsToTran` — recovering
`(p \in Msgs) ~> (p \in known_messages[a])` for every live a. The termination
theorems keep their `<>(p \in Msgs)` trigger and gain only `/\ TranFairness(p)`.
`CTranFairnessTransfer` gives the concrete counterpart
(`CSpec /\ CTranFairness(p) => TranFairness(p)`) via the unchanged
`CWFTransferAt`.

## Module inventory

Definitions (`HPaxosPlusCal`): `LiveRelevant`, `relevant_receive`, weakened
`NetworkAssumption`, `TranFairness`, `RelevantMsgs`; `CP_LT/CP_Good/CPLop`,
`KLT`, `LLTop`, `EKLT`, `EventuallyKnownInvariant` sources moved to
`RelevantMsgs`; new `CPT_*`/`KLTT`/`LLTTop` family (TranFairness flavour,
plain `Msgs` sources); new bridge ops `NBRop`, `BTCRop`, `BMNRop`,
`RelStableOp`, `RelSubNetOp`. (`HPaxosPlusCalConcrete`): `CRelevantStep`,
weakened `CNetworkAssumption`, `CTranFairness`.

New modules — weak chain: `RelBridge`, `BoxRelTranClosed`, `RelMono`,
`RelStable`, `BoxMemInRel`, `RelSubNet`, `RelevantLearnEnabled`. Tran chain:
`TranFairnessInst`, `LearnLeadsToTran(+W)`, `ConjPairLeadsToTran`,
`KnowLeadsToTran(+W)`. Concrete: `CRelWFTransferAt`, `CTranFairnessTransfer`.

Modified proofs: `NetworkAssumptionInst`, `LearnLeadsTo(+W)`,
`ConjPairLeadsTo`, `KnowLeadsTo(+W)`, `EventuallyKnown`,
`AlwaysEventuallyKnownInvariant`, `TwoAStepLtProduceR`,
`DepthZeroLeadsToR(+RW)`, `TerminatingProposalFreshOneBsR`,
`TerminatingProposalTwoAInductionR`, `TerminatingProposalRelaxed`,
`TerminatingProposal`, `Termination`, `CLivenessTransfer`.

Unchanged but re-verified (their statements survive as-is):
`TerminatingProposalTwoAStepR`, `TemporalDecideableProposalExists`,
`EKExtract`, `CWFTransferAt`, `CEnabledTransfer`,
`CAlwaysEventuallyKnownInvariant`, and all Msgs-source bridges
(`NetBridge`, `BoxTranClosed`, `NetStable`, ...), now serving the Tran chain.
