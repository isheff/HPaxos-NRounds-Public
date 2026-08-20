----------------------- MODULE OneBConstructBoundedRW -----------------------
EXTENDS HPaxosPlusCal, OneBConstructBoundedR

\* Thin wrapper for OneBConstructBoundedR.
LEMMA OneBConstructBoundedRW ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, self \in LiveAcceptors,
         NEW p \in Proposals, NEW bal \in Ballots,
         OneBCBHypR(self, p, bal)
  PROVE \E known \in SUBSET Messages :
        /\ known \subseteq Msgs
        /\ self \notin CaughtS(TranClosure(known \cup {p}))
        /\ (\A w \in known : (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p))))
        /\ \E y \in (Messages \ Proposals) :
             /\ Sig(y) = self
             /\ TranExclusive(y) = TranClosure(known \cup {p})
             /\ TranExclusive(y) = (known_messages[self] \cup {p}) \cup {mm \in Msgs : Sig(mm) = self}
             /\ B(y) = B(p)
             /\ IsOneB(y)
<1>h1. TranExclusive(p) \subseteq known_messages[self]  BY DEF OneBCBHypR
<1>h2. p \notin known_messages[self]  BY DEF OneBCBHypR
<1>h3. \A ww \in known_messages[self] : IsProposal(ww) => B(ww) # B(p)  BY DEF OneBCBHypR
<1>h4. \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= B(p)  BY DEF OneBCBHypR
<1>h5. self \notin CaughtS(TranClosure((known_messages[self] \cup {p})
                                        \cup {mm \in Msgs : Sig(mm) = self}))
  BY DEF OneBCBHypR
<1>h6. B(p) > bal  BY DEF OneBCBHypR
<1>h7. \A z \in Proposals : ((z \in RelevantMsgs) /\ (B(z) > bal)) =>
         ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))
  BY DEF OneBCBHypR
<1> QED BY <1>h1, <1>h2, <1>h3, <1>h4, <1>h5, <1>h6, <1>h7, OneBConstructBoundedR
====================================================================
