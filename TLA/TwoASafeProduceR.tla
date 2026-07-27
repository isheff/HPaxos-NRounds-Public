--------------------------- MODULE TwoASafeProduceR ---------------------------
EXTENDS HPaxosPlusCal, FiniteSetTheorems, BBallot, QuorumUpward,
        TwoAHoldsT, KnownSubAll
LOCAL INSTANCE TLAPS

\* Relaxed clone of TwoASafeProduce: the uniqueness hypothesis is weakened to
\* the relaxed form; its only use was the proposal-ballot <= B(p) bound, which
\* both disjuncts of the relaxed form supply.
LEMMA TwoASafeProduceR ==
  ASSUME MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions,
         AcceptorsAssumptions,
         NEW alpha \in Learners, NEW am \in SUBSET Messages, NEW bal \in Ballots, NEW p \in Proposals,
         NEW d \in Nat, d + 1 \in 1..MaxDepth(alpha), B(p) \in Ballots, B(p) > bal,
         NEW s \in SafeAcceptors, NEW WP,
         LiveAcceptors \in Quorums(alpha),
         \A x \in am : ((IsProposal(x) /\ (B(x) > bal)) =>
           ((V(x) = V(p)) /\ ((B(x) < B(p)) \/ (x = p)))),
         \A w \in WP : (B(w) = B(p) /\ HasDepth(alpha, w, d) /\ Sig(w) \in Acceptors),
         \A aa \in LiveAcceptors : \E w \in WP : Sig(w) = aa
  PROVE  TwoASafeConcl(am, alpha, p, d, s, WP)
<1> USE DEF TwoASafeConcl
<1>fa. IsFiniteSet(Acceptors)  BY DEF LearnerGraphAssumptions, FiniteAcceptors
<1>ti. Spec => []TwoAInvariantT  BY TwoAHoldsT
<1>de. (d + 1) - 1 = d  OBVIOUS
<1>1. Init => ((TwoAInvariantT /\ (\A xx : xx \in known_messages[s] => xx \in am)
                /\ WP \subseteq known_messages[s])
               => (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1)))
  <2> SUFFICES ASSUME TwoAInvariantT, \A xx : xx \in known_messages[s] => xx \in am,
                      WP \subseteq known_messages[s]
               PROVE  \E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1)
    OBVIOUS
  <2> DEFINE QS == {ww \in known_messages[s] : B(ww)=B(p) /\ HasDepth(alpha,ww,(d+1)-1)}
  <2>propb. \A ww \in known_messages[s] : IsProposal(ww) => B(ww) <= B(p)
    <3> SUFFICES ASSUME NEW ww \in known_messages[s], IsProposal(ww) PROVE B(ww) <= B(p)  OBVIOUS
    <3>1. ww \in am  OBVIOUS
    <3>wm. ww \in Messages  BY <3>1
    <3>btb. B(ww) \in Ballots  BY <3>wm, MessageInterfaceAssumptions, BBallot DEF MessageInterfaceAssumptions
    <3>bt. B(ww) \in Nat  BY <3>btb DEF Ballots
    <3>bn. bal \in Nat  BY DEF Ballots
    <3>pn. B(p) \in Nat  BY DEF Ballots
    <3>uq. B(ww) > bal => ((V(ww) = V(p)) /\ ((B(ww) < B(p)) \/ (ww = p)))  BY <3>1
    <3>cg. ww = p => B(ww) = B(p)  OBVIOUS
    <3> QED  BY <3>bt, <3>bn, <3>pn, <3>uq, <3>cg
  <2>qs. LiveAcceptors \subseteq SigS(QS)
    <3> SUFFICES ASSUME NEW aa \in LiveAcceptors PROVE aa \in SigS(QS)  OBVIOUS
    <3>1. PICK w \in WP : Sig(w)=aa  OBVIOUS
    <3>2. w \in known_messages[s]  BY <3>1
    <3>3. B(w)=B(p) /\ HasDepth(alpha,w,d)  BY <3>1
    <3>4. w \in QS  BY <3>2, <3>3, <1>de
    <3> QED  BY <3>4, <3>1 DEF SigS
  <2>acc. SigS(QS) \subseteq Acceptors
    <3> SUFFICES ASSUME NEW aa \in SigS(QS) PROVE aa \in Acceptors  OBVIOUS
    <3>1. PICK ww \in QS : aa = Sig(ww)  BY DEF SigS
    <3>2. HasDepth(alpha, ww, (d+1)-1)  BY <3>1
    <3> QED  BY <3>1, <3>2 DEF HasDepth
  <2>fin. IsFiniteSet(SigS(QS))  BY <2>acc, <1>fa, FS_Subset
  <2>lq. LiveAcceptors \in Quorums(alpha)  OBVIOUS
  <2>quo. SigS(QS) \in Quorums(alpha)  BY <2>lq, <2>qs, <2>acc, <2>fin, QuorumUpward
  <2> QED  BY <2>propb, <2>quo, TwoAInvariantT DEF TwoAInvariantT
<1>2. ((TwoAInvariantT /\ (\A xx : xx \in known_messages[s] => xx \in am)
        /\ WP \subseteq known_messages[s])
       => (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1))) /\ [Next]_vars
      => ((TwoAInvariantT /\ (\A xx : xx \in known_messages[s] => xx \in am)
           /\ WP \subseteq known_messages[s])
          => (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1)))'
  <2> SUFFICES ASSUME TwoAInvariantT', (\A xx : xx \in known_messages[s] => xx \in am)',
                      (WP \subseteq known_messages[s])'
               PROVE  (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1))'
    OBVIOUS
  <2> DEFINE QSp == {ww \in known_messages'[s] : B(ww)=B(p) /\ HasDepth(alpha,ww,(d+1)-1)}
  <2>ti2. TwoAInvariantT'  OBVIOUS
  <2>ks2. \A xx : xx \in known_messages'[s] => xx \in am  OBVIOUS
  <2>ws2. WP \subseteq known_messages'[s]  OBVIOUS
  <2>propb. \A ww \in known_messages'[s] : IsProposal(ww) => B(ww) <= B(p)
    <3> SUFFICES ASSUME NEW ww \in known_messages'[s], IsProposal(ww) PROVE B(ww) <= B(p)  OBVIOUS
    <3>1. ww \in am  BY <2>ks2
    <3>wm. ww \in Messages  BY <3>1
    <3>btb. B(ww) \in Ballots  BY <3>wm, MessageInterfaceAssumptions, BBallot DEF MessageInterfaceAssumptions
    <3>bt. B(ww) \in Nat  BY <3>btb DEF Ballots
    <3>bn. bal \in Nat  BY DEF Ballots
    <3>pn. B(p) \in Nat  BY DEF Ballots
    <3>uq. B(ww) > bal => ((V(ww) = V(p)) /\ ((B(ww) < B(p)) \/ (ww = p)))  BY <3>1
    <3>cg. ww = p => B(ww) = B(p)  OBVIOUS
    <3> QED  BY <3>bt, <3>bn, <3>pn, <3>uq, <3>cg
  <2>qs. LiveAcceptors \subseteq SigS(QSp)
    <3> SUFFICES ASSUME NEW aa \in LiveAcceptors PROVE aa \in SigS(QSp)  OBVIOUS
    <3>1. PICK w \in WP : Sig(w)=aa  OBVIOUS
    <3>2. w \in known_messages'[s]  BY <3>1, <2>ws2
    <3>3. B(w)=B(p) /\ HasDepth(alpha,w,d)  BY <3>1
    <3>4. w \in QSp  BY <3>2, <3>3, <1>de
    <3> QED  BY <3>4, <3>1 DEF SigS
  <2>acc. SigS(QSp) \subseteq Acceptors
    <3> SUFFICES ASSUME NEW aa \in SigS(QSp) PROVE aa \in Acceptors  OBVIOUS
    <3>1. PICK ww \in QSp : aa = Sig(ww)  BY DEF SigS
    <3>2. HasDepth(alpha, ww, (d+1)-1)  BY <3>1
    <3> QED  BY <3>1, <3>2 DEF HasDepth
  <2>fin. IsFiniteSet(SigS(QSp))  BY <2>acc, <1>fa, FS_Subset
  <2>lq. LiveAcceptors \in Quorums(alpha)  OBVIOUS
  <2>quo. SigS(QSp) \in Quorums(alpha)  BY <2>lq, <2>qs, <2>acc, <2>fin, QuorumUpward
  <2>ex. \E twoa \in Msgs' : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1)
    BY <2>propb, <2>quo, <2>ti2 DEF TwoAInvariantT
  <2> QED  BY <2>ex
<1>3. Spec => [](( TwoAInvariantT /\ (\A xx : xx \in known_messages[s] => xx \in am)
                  /\ WP \subseteq known_messages[s])
                 => (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1)))
  BY <1>1, <1>2, PTL DEF Spec
<1> SUFFICES ASSUME Spec, IsAllMessagesEverSent(am)
             PROVE  [](WP \subseteq known_messages[s]
                       => (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1)))
  OBVIOUS
<1>tib. []TwoAInvariantT  BY <1>ti
<1>ka. [](\A xx : xx \in known_messages[s] => xx \in am)  BY KnownSubAll DEF KnownAllBoxOp
<1>bodyb. [](( TwoAInvariantT /\ (\A xx : xx \in known_messages[s] => xx \in am)
              /\ WP \subseteq known_messages[s])
             => (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1)))
  BY <1>3
<1> QED  BY <1>tib, <1>ka, <1>bodyb, PTL
====================================================================
