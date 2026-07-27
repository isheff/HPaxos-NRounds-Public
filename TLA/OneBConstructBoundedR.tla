----------------------- MODULE OneBConstructBoundedR -----------------------
EXTENDS HPaxosPlusCal, BBallot, OneBConstructT,
        TranClosureSingleton, TranClosureUnion, TranClosureExpanding,
        SelfKnownClassifiedR

\* Relaxed clone of OneBConstructBoundedT: constructs the forced-send 1B at the
\* learn-p step and packages the witness "known" set with the CLASSIFIED bound
\* (low, or V(p)-valued strictly below B(p)) instead of the flat <= bal bound.
LEMMA OneBConstructBoundedR ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, NEW p \in Proposals, NEW bal \in Ballots,
         TranExclusive(p) \subseteq known_messages[self],
         p \notin known_messages[self],
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) # B(p),
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= B(p),
         self \notin CaughtS(TranClosure((known_messages[self] \cup {p})
                                          \cup {mm \in Msgs : Sig(mm) = self})),
         B(p) > bal,
         \A z \in Proposals : ((z \in Msgs) /\ (B(z) > bal)) =>
           ((V(z) = V(p)) /\ ((B(z) < B(p)) \/ (z = p)))
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
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
  BY DEF Inv
<1> DEFINE KP == known_messages[self] \cup {p}
<1> DEFINE SS == {mm \in Msgs : Sig(mm) = self}
<1> DEFINE T == KP \cup SS
<1>mi. TypeOKMessageInterface /\ TranFinite /\ AlwaysAProposal  BY DEF MessageInterfaceAssumptions
<1>pmsg. p \in Messages  BY <1>mi DEF TypeOKMessageInterface
<1>bpnat. B(p) \in Ballots  BY <1>pmsg, <1>mi, BBallot
<1>bpWit. \E bb \in Ballots : bb = B(p)  BY <1>bpnat
<1> PICK bb \in Ballots : bb = B(p)  BY <1>bpWit
<1>ex. \E y \in (Messages \ Proposals) :
         /\ Sig(y) = self
         /\ TranExclusive(y) = T
         /\ B(y) = bb
         /\ IsOneB(y)
  BY <1>pmsg, Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT, OneBConstructT
    DEF IsProposal
<1> PICK y \in (Messages \ Proposals) :
      /\ Sig(y) = self
      /\ TranExclusive(y) = T
      /\ B(y) = bb
      /\ IsOneB(y)
  BY <1>ex
<1>known. known_messages[self] \subseteq Msgs  BY <1>i
<1>tcKP. TranClosure(KP) = KP
  <2>1. TranClosure(known_messages[self]) = known_messages[self]
    BY KnownTranClosureInvT DEF KnownTranClosureInvT
  <2>2. TranClosure({p}) = Tran(p)  BY TranClosureSingleton
  <2>3. TranClosure(KP) = TranClosure(known_messages[self]) \cup TranClosure({p})
    BY TranClosureUnion
  <2>4. TranExclusive(p) \subseteq KP  OBVIOUS
  <2>5. Tran(p) \subseteq KP
    <3>a. p \in KP  OBVIOUS
    <3>b. Tran(p) = {p} \cup TranExclusive(p)  BY DEF Tran, TranExclusive
    <3> QED BY <2>4, <3>a, <3>b
  <2> QED BY <2>1, <2>2, <2>3, <2>5, TranClosureExpanding
<1>ssb. \A z \in Msgs : Sig(z) = self => TranExclusive(z) \subseteq KP \cup SS
  <2> SUFFICES ASSUME NEW z \in Msgs, Sig(z) = self
               PROVE TranExclusive(z) \subseteq KP \cup SS  OBVIOUS
  <2>1. TranExclusive(z) \subseteq known_messages[self] \cup SS  BY SelfSentBoundedInvT DEF SelfSentBoundedInvT
  <2> QED BY <2>1
<1>tcSS. TranClosure(SS) \subseteq T
  <2> SUFFICES ASSUME NEW z \in TranClosure(SS) PROVE z \in T  OBVIOUS
  <2>1. PICK w \in SS : z \in Tran(w)  BY DEF TranClosure
  <2>2. z = w \/ z \in TranExclusive(w)  BY <2>1 DEF Tran, TranExclusive
  <2>3. w \in Msgs /\ Sig(w) = self  BY <2>1
  <2>4. TranExclusive(w) \subseteq KP \cup SS  BY <2>3, <1>ssb
  <2> QED BY <2>1, <2>2, <2>4
<1>tcTeq. TranClosure(T) = TranClosure(KP) \cup TranClosure(SS)  BY TranClosureUnion
<1>tcT. TranClosure(T) = T
  <2>sub1. TranClosure(T) \subseteq T  BY <1>tcTeq, <1>tcKP, <1>tcSS
  <2>sub2. T \subseteq TranClosure(T)  BY TranClosureExpanding
  <2> QED BY <2>sub1, <2>sub2
<1>pnotss. p \notin SS
  <2> SUFFICES ASSUME p \in SS PROVE FALSE  OBVIOUS
  <2>1. p \in Msgs /\ Sig(p) = self  OBVIOUS
  <2>2. ~IsProposal(p)  BY <2>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
  <2> QED BY <2>2 DEF IsProposal
<1> DEFINE known == known_messages[self] \cup SS
<1>keq. known \cup {p} = T  BY <1>pnotss
<1>tep. TranExclusive(y) = TranClosure(known \cup {p})  BY <1>keq, <1>tcT
<1>knownmsgs. known \subseteq Messages  BY <1>known, <1>i
<1>knownclass. \A w \in known : (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p)))
  <2> SUFFICES ASSUME NEW w \in known
               PROVE (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p)))  OBVIOUS
  <2>1. w \in known_messages[self] \/ w \in SS  BY DEF known
  <2> QED BY <2>1, MessageInterfaceAssumptions, LearnerGraphAssumptions, Inv,
             KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
             SelfKnownClassifiedR
<1>knownnet. \A w \in known : w \in Msgs
  <2> SUFFICES ASSUME NEW w \in known PROVE w \in Msgs  OBVIOUS
  <2>1. w \in known_messages[self] \/ w \in SS  BY DEF known
  <2> QED BY <2>1, <1>known
<1>selfnotcaught. self \notin CaughtS(TranClosure(known \cup {p}))  BY <1>keq
<1>kWit. \E kk \in SUBSET Messages : kk = known  BY <1>knownmsgs
<1> PICK kk \in SUBSET Messages : kk = known  BY <1>kWit
<1> QED
  <2> WITNESS kk \in SUBSET Messages
  <2>1. kk \subseteq Msgs  BY <1>knownnet
  <2>2. self \notin CaughtS(TranClosure(kk \cup {p}))  BY <1>selfnotcaught
  <2>3. \A w \in kk : (B(w) <= bal) \/ ((B(w) < B(p)) /\ (V(w) = V(p)))  BY <1>knownclass
  <2>4. \E w \in (Messages \ Proposals) :
          /\ Sig(w) = self
          /\ TranExclusive(w) = TranClosure(kk \cup {p})
          /\ TranExclusive(w) = (known_messages[self] \cup {p}) \cup {mm \in Msgs : Sig(mm) = self}
          /\ B(w) = B(p)
          /\ IsOneB(w)
    <3> WITNESS y \in (Messages \ Proposals)
    <3> QED BY <1>tep, <1>keq, <1>tcT
  <2> QED BY <2>1, <2>2, <2>3, <2>4
====================================================================
