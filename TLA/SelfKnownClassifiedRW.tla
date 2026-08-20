------------------------ MODULE SelfKnownClassifiedRW ------------------------
EXTENDS HPaxosPlusCal, SelfKnownClassifiedR

\* Thin wrapper for SelfKnownClassifiedR (heavy-ambient citation guard).
LEMMA SelfKnownClassifiedRW ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, self \in LiveAcceptors,
         NEW p \in Proposals, NEW bal \in Ballots,
         SelfKnownHypR(self, p, bal)
  PROVE \A w \in (known_messages[self] \cup {mm \in Msgs : Sig(mm) = self}) :
          (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p)))
<1>h1. B(p) > bal  BY DEF SelfKnownHypR
<1>h2. p \notin known_messages[self]  BY DEF SelfKnownHypR
<1>h3. \A z \in Proposals : ((z \in RelevantMsgs) /\ (B(z) > bal)) =>
         ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))
  BY DEF SelfKnownHypR
<1> QED BY <1>h1, <1>h2, <1>h3, SelfKnownClassifiedR
====================================================================
