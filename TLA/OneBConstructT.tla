--------------------------- MODULE OneBConstructT ---------------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        BAchievedByProposal, MaxBSetProperty, BBallot,
        TranClosureSingleton, TranClosureUnion, TranClosureExpanding,
        LeFromEqT, LeTransBallotsT, EqFromLeGeBallotsT

\* Core construction: within a learn step where self learns a genuinely-new
\* ballot-b proposal x with no other ballot-b proposal already known, the
\* forced-send mechanism's target set M is provably non-empty (AlwaysANewOneB),
\* and ANY witness the CHOOSE picks structurally satisfies B=b and IsOneB --
\* regardless of which specific witness is chosen.
LEMMA OneBConstructT ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, NEW x \in Messages, NEW b \in Ballots,
         TranExclusive(x) \subseteq known_messages[self],
         x \notin known_messages[self],
         IsProposal(x), B(x) = b,
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) # b,
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b,
         self \notin CaughtS(TranClosure((known_messages[self] \cup {x})
                                          \cup {mm \in Msgs : Sig(mm) = self}))
  PROVE \E y \in (Messages \ Proposals) :
          /\ Sig(y) = self
          /\ TranExclusive(y) = (known_messages[self] \cup {x}) \cup {mm \in Msgs : Sig(mm) = self}
          /\ B(y) = b
          /\ IsOneB(y)
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
  BY DEF Inv
<1>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal /\ AlwaysANewOneB
  BY DEF MessageInterfaceAssumptions
<1>selfacc. self \in Acceptors  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption
<1> DEFINE KP == known_messages[self] \cup {x}
<1> DEFINE T == KP \cup {mm \in Msgs : Sig(mm) = self}
<1>kpmsgs. KP \subseteq Messages  BY <1>i
<1>tmsgs. T \subseteq Messages  BY <1>kpmsgs, <1>i
<1>tfin. IsFiniteSet(T)
  <2>0. known_messages[self] \subseteq Msgs  BY <1>i
  <2>0b. IsFiniteSet(known_messages[self])  BY <2>0, <1>i, FS_Subset
  <2>1. IsFiniteSet(KP)  BY <2>0b, FS_AddElement
  <2>2. IsFiniteSet({mm \in Msgs : Sig(mm) = self})  BY <1>i, FS_Subset
  <2> QED BY <2>1, <2>2, FS_Union
<1>noneknown. \A w \in known_messages[self] : B(w) # b
  <2> SUFFICES ASSUME NEW w \in known_messages[self], B(w) = b PROVE FALSE  OBVIOUS
  <2>wm. w \in Messages  BY <1>i
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = b  BY <2>wm, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = b  BY <2>ach
  <2>qk. q \in known_messages[self]  BY KnownTranClosureInvT DEF KnownTranClosureInvT, TranClosure
  <2> QED BY <2>qk
<1>xpropbal. ProposalBal(x) = b
  <2>ach. \E q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = B(x) /\ B(q) = B(x)  BY BAchievedByProposal
  <2> PICK q \in Tran(x) : IsProposal(q) /\ ProposalBal(q) = B(x) /\ B(q) = B(x)  BY <2>ach
  <2>qcase. q = x \/ q \in TranExclusive(x)  BY DEF Tran, TranExclusive
  <2>notother. q \in TranExclusive(x) => FALSE
    <3> SUFFICES ASSUME q \in TranExclusive(x) PROVE FALSE  OBVIOUS
    <3>1. q \in known_messages[self]  OBVIOUS
    <3> QED BY <3>1
  <2> QED BY <2>qcase, <2>notother
<1>tbound. \A w \in T : B(w) <= b
  <2> SUFFICES ASSUME NEW w \in T PROVE B(w) <= b  OBVIOUS
  <2>wm. w \in Messages  BY <1>tmsgs
  <2>ach. \E q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>wm, BAchievedByProposal
  <2> PICK q \in Tran(w) : IsProposal(q) /\ B(q) = B(w)  BY <2>ach
  <2>kpcase. CASE w \in KP
    <3>qw. q = w \/ q \in TranExclusive(w)  BY DEF Tran, TranExclusive
    <3>xcase. CASE w = x
      <4>1. B(w) = B(x)  BY <3>xcase
      <4>2. B(x) = b  OBVIOUS
      <4>3. B(w) = b  BY <4>1, <4>2
      <4>4. b \in Ballots  OBVIOUS
      <4>5. B(w) \in Ballots  BY <4>3, <4>4
      <4> QED BY <4>3, <4>4, <4>5, LeFromEqT
    <3>kcase. CASE w \in known_messages[self]
      <4>1. q = w \/ q \in known_messages[self]
        <5>1. TranExclusive(w) \subseteq known_messages[self]
          <6>a. Tran(w) \subseteq TranClosure(known_messages[self])  BY <3>kcase DEF TranClosure
          <6>b. TranClosure(known_messages[self]) = known_messages[self]
            BY KnownTranClosureInvT DEF KnownTranClosureInvT
          <6>c. TranExclusive(w) \subseteq Tran(w)  BY DEF Tran, TranExclusive
          <6> QED BY <6>a, <6>b, <6>c
        <5> QED BY <3>qw, <5>1
      <4>2. q \in known_messages[self]  BY <4>1, <3>kcase
      <4>3. IsProposal(q)  OBVIOUS
      <4>4. B(q) <= b  BY <4>2, <4>3
      <4>5. B(q) = B(w)  OBVIOUS
      <4> QED BY <4>4, <4>5
    <3> QED BY <3>xcase, <3>kcase, <2>kpcase
  <2>sscase. CASE w \in {mm \in Msgs : Sig(mm) = self}
    <3>notprop. ~IsProposal(w)
      <4>1. w \in Msgs /\ Sig(w) = self  BY <2>sscase
      <4> QED BY <4>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qnw. q # w  BY <3>notprop
    <3>qte. q \in TranExclusive(w)  BY <3>qnw DEF Tran, TranExclusive
    <3>bound2. TranExclusive(w) \subseteq known_messages[self] \cup {mm \in Msgs : Sig(mm) = self}
      BY <2>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>qkorself. q \in known_messages[self] \/ q \in {mm \in Msgs : Sig(mm) = self}
      BY <3>qte, <3>bound2
    <3>qisprop. IsProposal(q)  OBVIOUS
    <3>notselfprop. q \notin {mm \in Msgs : Sig(mm) = self}
      <4> SUFFICES ASSUME q \in {mm \in Msgs : Sig(mm) = self} PROVE FALSE  OBVIOUS
      <4>1. q \in Msgs /\ Sig(q) = self  OBVIOUS
      <4> QED BY <4>1, <3>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qk. q \in known_messages[self]  BY <3>qkorself, <3>notselfprop
    <3>qbound. B(q) <= b  BY <3>qk, <3>qisprop
    <3>qbw. B(q) = B(w)  OBVIOUS
    <3> QED BY <3>qbound, <3>qbw
  <2> QED BY <2>kpcase, <2>sscase
<1>tcT. TranClosure(T) = T
  <2>kc. TranClosure(KP) = KP
    <3>1. TranClosure(known_messages[self]) = known_messages[self]
      BY KnownTranClosureInvT DEF KnownTranClosureInvT
    <3>2. TranClosure({x}) = Tran(x)  BY TranClosureSingleton
    <3>3. TranClosure(KP) = TranClosure(known_messages[self]) \cup TranClosure({x})  BY TranClosureUnion
    <3>4. TranExclusive(x) \subseteq KP  OBVIOUS
    <3>5. Tran(x) \subseteq KP
      <4>a. x \in KP  OBVIOUS
      <4>b. Tran(x) = {x} \cup TranExclusive(x)  BY DEF Tran, TranExclusive
      <4> QED BY <3>4, <4>a, <4>b
    <3> QED BY <3>1, <3>2, <3>3, <3>5, TranClosureExpanding
  <2>ssb. \A z \in Msgs :
            Sig(z) = self => TranExclusive(z) \subseteq KP \cup {mm \in Msgs : Sig(mm) = self}
    <3> SUFFICES ASSUME NEW z \in Msgs, Sig(z) = self
                 PROVE TranExclusive(z) \subseteq KP \cup {mm \in Msgs : Sig(mm) = self}  OBVIOUS
    <3>1. TranExclusive(z) \subseteq known_messages[self] \cup {mm \in Msgs : Sig(mm) = self}
      BY SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3> QED BY <3>1
  <2>tcSS. TranClosure({mm \in Msgs : Sig(mm) = self}) \subseteq T
    <3> SUFFICES ASSUME NEW z \in TranClosure({mm \in Msgs : Sig(mm) = self}) PROVE z \in T  OBVIOUS
    <3>1. PICK w \in {mm \in Msgs : Sig(mm) = self} : z \in Tran(w)  BY DEF TranClosure
    <3>2. z = w \/ z \in TranExclusive(w)  BY <3>1 DEF Tran, TranExclusive
    <3>3. w \in Msgs /\ Sig(w) = self  BY <3>1
    <3>4. TranExclusive(w) \subseteq KP \cup {mm \in Msgs : Sig(mm) = self}  BY <3>3, <2>ssb
    <3> QED BY <3>1, <3>2, <3>4
  <2>tcTeq. TranClosure(T) = TranClosure(KP) \cup TranClosure({mm \in Msgs : Sig(mm) = self})
    BY TranClosureUnion
  <2>sub1. TranClosure(T) \subseteq T  BY <2>tcTeq, <2>kc, <2>tcSS
  <2>sub2. T \subseteq TranClosure(T)  BY TranClosureExpanding
  <2> QED BY <2>sub1, <2>sub2
<1>tset. {z \in TranClosure(T) : B(z) = b} = {x}
  <2> SUFFICES ASSUME NEW z \in TranClosure(T), B(z) = b PROVE z = x  BY <1>tcT
  <2>zt. z \in T  BY <1>tcT
  <2>ach. \E q \in Tran(z) : IsProposal(q) /\ B(q) = b  BY <1>tmsgs, <2>zt, BAchievedByProposal
  <2> PICK q \in Tran(z) : IsProposal(q) /\ B(q) = b  BY <2>ach
  <2>kpcase. CASE z \in KP
    <3>qz. q = z \/ q \in TranExclusive(z)  BY DEF Tran, TranExclusive
    <3>xcase. CASE z = x  BY <3>xcase
    <3>kcase. CASE z \in known_messages[self]
      <4>1. q = z \/ q \in known_messages[self]
        <5>1. TranExclusive(z) \subseteq known_messages[self]
          BY <3>kcase, KnownTranClosureInvT DEF KnownTranClosureInvT, TranClosure, Tran
        <5> QED BY <3>qz, <5>1
      <4>2. CASE q = z  BY <4>2, <3>kcase
      <4>3. CASE q \in known_messages[self]  BY <4>3, <1>noneknown
      <4> QED BY <4>1, <4>2, <4>3
    <3> QED BY <3>xcase, <3>kcase, <2>kpcase
  <2>sscase. CASE z \in {mm \in Msgs : Sig(mm) = self}
    <3>notprop. ~IsProposal(z)
      <4>1. z \in Msgs /\ Sig(z) = self  BY <2>sscase
      <4> QED BY <4>1, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qnz. q # z  BY <3>notprop
    <3>qte. q \in TranExclusive(z)  BY <3>qnz DEF Tran, TranExclusive
    <3>bound2. TranExclusive(z) \subseteq known_messages[self] \cup {mm \in Msgs : Sig(mm) = self}
      BY <2>sscase, SelfSentBoundedInvT DEF SelfSentBoundedInvT
    <3>qkorself. q \in known_messages[self] \/ q \in {mm \in Msgs : Sig(mm) = self}
      BY <3>qte, <3>bound2
    <3>qisprop. IsProposal(q)  OBVIOUS
    <3>notselfprop. q \notin {mm \in Msgs : Sig(mm) = self}
      <4> SUFFICES ASSUME q \in {mm \in Msgs : Sig(mm) = self} PROVE FALSE  OBVIOUS
      <4>1. q \in Msgs /\ Sig(q) = self  OBVIOUS
      <4> QED BY <4>1, <3>qisprop, SelfSentNotProposalInvT DEF SelfSentNotProposalInvT
    <3>qk. q \in known_messages[self]  BY <3>qkorself, <3>notselfprop
    <3>qbeqb. B(q) = b  OBVIOUS
    <3>qbneqb. B(q) # b  BY <3>qk, <1>noneknown
    <3> QED BY <3>qbeqb, <3>qbneqb
  <2>zdisj. z \in KP \/ z \in {mm \in Msgs : Sig(mm) = self}  BY <2>zt
  <2> QED BY <2>zdisj, <2>kpcase, <2>sscase
<1>xint. x \in TranClosure(T)  BY <1>tcT, TranClosureExpanding
<1>card1. Cardinality({z \in TranClosure(T) : B(z) = b}) = 1  BY <1>tset, FS_Singleton
<1>uncaught. self \notin CaughtS(TranClosure(T))  OBVIOUS \* matches the lemma's own hypothesis verbatim (T's literal expansion)
<1>anb. \E y \in Messages :
          /\ Sig(y) = self
          /\ self \notin Caught(y)
          /\ IsOneB(y)
          /\ TranExclusive(y) = TranClosure(T)
  BY <1>mi, <1>selfacc, <1>tmsgs, <1>tfin, <1>tbound, <1>card1, <1>uncaught DEF AlwaysANewOneB
<1> PICK y \in Messages :
      /\ Sig(y) = self
      /\ self \notin Caught(y)
      /\ IsOneB(y)
      /\ TranExclusive(y) = TranClosure(T)
  BY <1>anb
<1>ytc. TranExclusive(y) = T  BY <1>tcT
<1>ynotprop. y \notin Proposals  BY DEF IsOneB, IsProposal
<1>ybal. B(y) = b
  <2> DEFINE Cand == Proposals \cap Tran(y)
  <2>tranY. Tran(y) = {y} \cup T  BY <1>ytc DEF Tran, TranExclusive
  <2>candeq. Cand = Proposals \cap T
    <3>1. y \notin Proposals  BY <1>ynotprop
    <3> QED BY <2>tranY, <3>1
  <2>xincand. x \in Cand
    <3>a. x \in Proposals  BY DEF IsProposal
    <3>b. x \in T  OBVIOUS
    <3> QED BY <2>candeq, <3>a, <3>b
  <2>ubound. \A z \in Cand : ProposalBal(z) <= b
    <3> SUFFICES ASSUME NEW z \in Cand PROVE ProposalBal(z) <= b  OBVIOUS
    <3>1. z \in T  BY <2>candeq
    <3>2. IsProposal(z)  BY <2>candeq DEF IsProposal
    <3>3. z \in Messages  BY <3>1, <1>tmsgs
    <3>4. z \in GetProposals(z)
      <4>1. z \in Tran(z)  BY DEF Tran
      <4> QED BY <4>1, <2>candeq DEF GetProposals
    <3>5. ProposalBal(z) <= B(z)
      <4>fin. IsFiniteSet(GetProposals(z))
        <5>1. GetProposals(z) \subseteq Tran(z)  BY DEF GetProposals
        <5>2. IsFiniteSet(Tran(z))  BY <3>3, <1>mi DEF TranFinite
        <5> QED BY <5>1, <5>2, FS_Subset
      <4>sub. GetProposals(z) \subseteq Proposals  BY DEF GetProposals
      <4>ne. GetProposals(z) # {}  BY <3>4
      <4>choose. /\ B(z) \in {ProposalBal(w) : w \in GetProposals(z)}
                 /\ \A ww \in {ProposalBal(w) : w \in GetProposals(z)} : B(z) >= ww
        BY <4>fin, <4>sub, <4>ne, <1>mi, MaxBSetProperty DEF B
      <4>mem. ProposalBal(z) \in {ProposalBal(w) : w \in GetProposals(z)}  BY <3>4
      <4> QED BY <4>choose, <4>mem
    <3>6. B(z) <= b  BY <3>1, <1>tbound
    <3>7. ProposalBal(z) \in Ballots
      <4>1. MessageInterface.proposalbal \in [Proposals -> Ballots]  BY <1>mi DEF TypeOKMessageInterface
      <4>2. z \in Proposals  BY <3>2 DEF IsProposal
      <4> QED BY <4>1, <4>2 DEF ProposalBal
    <3>8. B(z) \in Ballots  BY <1>mi, <3>3, BBallot
    <3>9. b \in Ballots  OBVIOUS
    <3> QED BY <3>5, <3>6, <3>7, <3>8, <3>9, LeTransBallotsT
  <2>xbal. ProposalBal(x) = b  BY <1>xpropbal
  <2>candfin. IsFiniteSet(Cand)
    <3>ysub. Cand \subseteq Tran(y)  OBVIOUS
    <3>yfin. IsFiniteSet(Tran(y))  BY <1>mi DEF TranFinite
    <3> QED BY <3>ysub, <3>yfin, FS_Subset
  <2>candsub. Cand \subseteq Proposals  OBVIOUS
  <2>candne. Cand # {}  BY <2>xincand
  <2>ychoose. /\ B(y) \in {ProposalBal(w) : w \in Cand}
              /\ \A ww \in {ProposalBal(w) : w \in Cand} : B(y) >= ww
    BY <2>candfin, <2>candsub, <2>candne, <1>mi, MaxBSetProperty DEF B, GetProposals
  <2>yge. B(y) >= b
    <3>1. ProposalBal(x) \in {ProposalBal(w) : w \in Cand}  BY <2>xincand
    <3> QED BY <3>1, <2>ychoose, <2>xbal
  <2>yle. B(y) <= b
    <3>pw. PICK w \in Cand : B(y) = ProposalBal(w)  BY <2>ychoose
    <3> QED BY <3>pw, <2>ubound
  <2>yty. y \in Messages  OBVIOUS
  <2>ybalty. B(y) \in Ballots  BY <1>mi, <2>yty, BBallot
  <2>bty. b \in Ballots  OBVIOUS
  <2> QED BY <2>yge, <2>yle, <2>ybalty, <2>bty, EqFromLeGeBallotsT
<1>xney. x # y
  <2>xprop. x \in Proposals  BY DEF IsProposal
  <2> QED BY <2>xprop, <1>ynotprop
<1>yisoneb. IsOneB(y)
  <2>cardxy. {z \in Tran(y) : B(z) = b} = {x, y}
    <3>tranY. Tran(y) = {y} \cup T  BY <1>ytc DEF Tran, TranExclusive
    <3>seteq. {z \in T : B(z) = b} = {x}  BY <1>tset, <1>tcT
    <3> QED BY <3>tranY, <3>seteq, <1>ybal, <1>xney
  <2>card2. Cardinality({x, y}) = 2
    <3>1. IsFiniteSet({y})  BY FS_Singleton
    <3>2. Cardinality({y}) = 1  BY FS_Singleton
    <3>3. x \notin {y}  BY <1>xney
    <3>4. {x,y} = {x} \cup {y}  OBVIOUS
    <3> QED BY <3>1, <3>2, <3>3, <3>4, FS_AddElement
  <2> QED BY <2>cardxy, <2>card2, <1>ynotprop DEF IsOneB, IsProposal
<1> QED BY <1>ynotprop, <1>ytc, <1>ybal, <1>yisoneb DEF Proposals
====================================================================
