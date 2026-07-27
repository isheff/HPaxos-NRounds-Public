---------------------------- MODULE TwoAConstructT ----------------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems,
        BAchievedByProposal, TranClosureSingleton, TranClosureUnion,
        TranClosureExpanding, QuorumUpward, LeFromEqT, SigSFiniteT,
        AlwaysANewTwoAInstT

LEMMA TwoAConstructT ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         Inv, KnownTranClosureInvT, SelfSentBoundedInvT, SelfSentNotProposalInvT,
         NEW self \in SafeAcceptors, NEW x \in Messages, NEW b \in Ballots,
         NEW alpha \in Learners, NEW d \in (1..MaxDepth(alpha)),
         TranExclusive(x) \subseteq known_messages[self],
         B(x) = b, HasDepth(alpha, x, d-1),
         \A ww \in known_messages[self] : IsProposal(ww) => B(ww) <= b,
         SigS({xx \in (known_messages[self] \cup {x}) :
               B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha),
         self \notin CaughtS(TranClosure((known_messages[self] \cup {x})
                                          \cup {mm \in Msgs : Sig(mm) = self}))
  PROVE \E x2 \in Messages :
          /\ (x2 \in ((known_messages[self] \cup {x}) \cup {mm \in Msgs : Sig(mm) = self})
              \/ TranExclusive(x2) = ((known_messages[self] \cup {x}) \cup {mm \in Msgs : Sig(mm) = self}))
          /\ B(x2) = b
          /\ Sig(x2) = self
          /\ HasDepth(alpha, x2, d)
          /\ self \notin Caught(x2)
          /\ IsTwoA(x2)
<1>i. /\ Msgs \in SUBSET Messages
      /\ known_messages \in [SafeAcceptors -> SUBSET Messages]
      /\ IsFiniteSet(Msgs)
      /\ (\A s \in SafeAcceptors : known_messages[s] \subseteq Msgs)
  BY DEF Inv
<1>mi. TranFinite /\ TypeOKMessageInterface /\ AlwaysAProposal /\ TranTrans /\ TranAcyclic /\ AlwaysANewTwoA
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
<1> DEFINE FiltKP == {xx \in KP : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
<1> DEFINE FiltT == {xx \in T : B(xx) = b /\ HasDepth(alpha, xx, d-1)}
<1>quoT. SigS(FiltT) \in Quorums(alpha)
  <2>sub. FiltKP \subseteq FiltT  OBVIOUS
  <2>sigsub. SigS(FiltKP) \subseteq SigS(FiltT)  BY <2>sub DEF SigS
  <2>tfilt. FiltT \subseteq T  OBVIOUS
  <2>fin. IsFiniteSet(FiltT)  BY <2>tfilt, <1>tfin, FS_Subset
  <2>sigfin. IsFiniteSet(SigS(FiltT))  BY <2>fin, SigSFiniteT
  <2>acc. SigS(FiltT) \subseteq Acceptors
    <3> SUFFICES ASSUME NEW aa \in SigS(FiltT) PROVE aa \in Acceptors  OBVIOUS
    <3>1. PICK qq \in FiltT : aa = Sig(qq)  BY DEF SigS
    <3>2. HasDepth(alpha, qq, d-1)  BY <3>1
    <3>3. Sig(qq) \in Acceptors  BY <3>2 DEF HasDepth
    <3> QED BY <3>1, <3>3
  <2>quoKP. SigS(FiltKP) \in Quorums(alpha)  OBVIOUS
  <2> QED BY <2>quoKP, <2>sigsub, <2>sigfin, <2>acc, QuorumUpward, <1>tcT
<1>uncaughtT. self \notin CaughtS(TranClosure(T))  OBVIOUS
<1>tinSM. T \in SUBSET Messages  BY <1>tmsgs
<1>dtyp. d \in (1..MaxDepth(alpha))  OBVIOUS
<1>anhyps. /\ self \in Acceptors
          /\ T \in SUBSET Messages
          /\ d \in (1..MaxDepth(alpha))
          /\ IsFiniteSet(T)
          /\ (\A ww \in T : B(ww) <= b)
          /\ SigS({xx \in TranClosure(T) : B(xx) = b /\ HasDepth(alpha, xx, d-1)}) \in Quorums(alpha)
          /\ self \notin CaughtS(TranClosure(T))
  BY <1>selfacc, <1>tinSM, <1>dtyp, <1>tfin, <1>tbound, <1>quoT, <1>uncaughtT, <1>tcT
<1>anb. \E x2 \in Messages :
          /\ (x2 \in TranClosure(T) \/ TranClosure(T) = TranExclusive(x2))
          /\ B(x2) = b
          /\ Sig(x2) = self
          /\ HasDepth(alpha, x2, d)
          /\ self \notin Caught(x2)
          /\ IsTwoA(x2)
  BY <1>anhyps, MessageInterfaceAssumptions, AlwaysANewTwoAInstT
<1> PICK x2 \in Messages :
      /\ (x2 \in TranClosure(T) \/ TranClosure(T) = TranExclusive(x2))
      /\ B(x2) = b
      /\ Sig(x2) = self
      /\ HasDepth(alpha, x2, d)
      /\ self \notin Caught(x2)
      /\ IsTwoA(x2)
  BY <1>anb
<1>disj. x2 \in T \/ TranExclusive(x2) = T  BY <1>tcT
<1> QED BY <1>disj
====================================================================
