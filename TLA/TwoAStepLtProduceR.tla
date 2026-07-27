-------------------------- MODULE TwoAStepLtProduceR --------------------------
EXTENDS HPaxosPlusCal, TwoASafeProduceR,
        AlwaysEventuallyKnownInvariant, EKExtract
LOCAL INSTANCE TLAPS

\* Relaxed clone of TwoAStepLtProduce.
LEMMA TwoAStepLtProduceR ==
  ASSUME MessageInterfaceAssumptions, ValueInterfaceAssumptions, LearnerGraphAssumptions,
         AcceptorsAssumptions,
         NEW alpha \in Learners, NEW am \in SUBSET Messages, NEW bal \in Ballots, NEW p \in Proposals,
         NEW d \in Nat, d + 1 \in 1..MaxDepth(alpha), B(p) \in Ballots, B(p) > bal,
         LiveAcceptors \in Quorums(alpha),
         \A x \in am : ((IsProposal(x) /\ (B(x) > bal)) =>
           ((V(x) = V(p)) /\ ((B(x) < B(p)) \/ (x = p)))),
         LiveAcceptorsSentDepthBallot(am, alpha, B(p), d)
  PROVE  IsAllMessagesEverSent(am) => (\A s \in LiveAcceptors : TwoAStepLtOp(am, alpha, p, d, s))
<1>ldsb. LiveAcceptors \subseteq SigS({x \in am : B(x) = B(p) /\ HasDepth(alpha, x, d)})
  BY DEF LiveAcceptorsSentDepthBallot
<1>ch. \A aa \in LiveAcceptors :
         LET w == CHOOSE x \in am : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))
         IN w \in am /\ Sig(w)=aa /\ B(w)=B(p) /\ HasDepth(alpha,w,d)
  <2> SUFFICES ASSUME NEW aa \in LiveAcceptors
               PROVE  LET w == CHOOSE x \in am : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))
                      IN w \in am /\ Sig(w)=aa /\ B(w)=B(p) /\ HasDepth(alpha,w,d)
    OBVIOUS
  <2>ne. \E x \in am : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))  BY <1>ldsb DEF SigS
  <2> QED  BY <2>ne
<1>wshape. \A w \in WPrimeStep(am, alpha, p, d) :
             B(w) = B(p) /\ HasDepth(alpha, w, d) /\ Sig(w) \in Acceptors
  <2> SUFFICES ASSUME NEW w \in WPrimeStep(am, alpha, p, d)
               PROVE  B(w) = B(p) /\ HasDepth(alpha, w, d) /\ Sig(w) \in Acceptors
    OBVIOUS
  <2>1. PICK aa \in LiveAcceptors :
          w = CHOOSE x \in am : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))
    BY DEF WPrimeStep
  <2>2. Sig(w)=aa /\ B(w)=B(p) /\ HasDepth(alpha,w,d)  BY <2>1, <1>ch
  <2>3. aa \in Acceptors  BY DEF AcceptorsAssumptions, SafeAcceptorsAssumption, LiveAcceptorsAssumption
  <2> QED  BY <2>2, <2>3
<1>wsig. \A aa \in LiveAcceptors : \E w \in WPrimeStep(am, alpha, p, d) : Sig(w) = aa
  <2> SUFFICES ASSUME NEW aa \in LiveAcceptors
               PROVE  \E w \in WPrimeStep(am, alpha, p, d) : Sig(w) = aa
    OBVIOUS
  <2>w. (CHOOSE x \in am : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))) \in WPrimeStep(am, alpha, p, d)
    BY DEF WPrimeStep
  <2>s. Sig(CHOOSE x \in am : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))) = aa  BY <1>ch
  <2> QED  BY <2>w, <2>s
<1>wsm. WPrimeStep(am, alpha, p, d) \in SUBSET Messages
  <2> SUFFICES ASSUME NEW w \in WPrimeStep(am, alpha, p, d) PROVE w \in Messages  OBVIOUS
  <2>1. PICK aa \in LiveAcceptors :
          w = CHOOSE x \in am : (Sig(x)=aa /\ B(x)=B(p) /\ HasDepth(alpha,x,d))
    BY DEF WPrimeStep
  <2>2. w \in am  BY <2>1, <1>ch
  <2> QED  BY <2>2
<1> SUFFICES ASSUME NEW s \in LiveAcceptors
             PROVE  IsAllMessagesEverSent(am) => TwoAStepLtOp(am, alpha, p, d, s)
  OBVIOUS
<1>ssafe. s \in SafeAcceptors  BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
\* the two boxed facts, proven while Spec/IsAll are NOT ambient (in the goal):
<1>elim. Spec => []((\A a \in LiveAcceptors : WPrimeStep(am, alpha, p, d) \subseteq known_messages[a])
                    => WPrimeStep(am, alpha, p, d) \subseteq known_messages[s])
  <2>1. Init => ((\A a \in LiveAcceptors : WPrimeStep(am, alpha, p, d) \subseteq known_messages[a])
                 => WPrimeStep(am, alpha, p, d) \subseteq known_messages[s])
    OBVIOUS
  <2>2. ((\A a \in LiveAcceptors : WPrimeStep(am, alpha, p, d) \subseteq known_messages[a])
         => WPrimeStep(am, alpha, p, d) \subseteq known_messages[s]) /\ [Next]_vars
        => ((\A a \in LiveAcceptors : WPrimeStep(am, alpha, p, d) \subseteq known_messages[a])
            => WPrimeStep(am, alpha, p, d) \subseteq known_messages[s])'
    OBVIOUS
  <2> QED  BY <2>1, <2>2, PTL DEF Spec
<1>safe0. TwoASafeConcl(am, alpha, p, d, s, WPrimeStep(am, alpha, p, d))
  BY <1>wshape, <1>wsig, <1>ssafe, TwoASafeProduceR
\* now bring in IsAll, Spec, NetworkAssumption and compose the leads-to:
<1> SUFFICES ASSUME IsAllMessagesEverSent(am), Spec, NetworkAssumption
             PROVE  (WPrimeStep(am, alpha, p, d) \subseteq Msgs)
                    ~> (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1))
  BY DEF TwoAStepLtOp
<1>ekinv. []EventuallyKnownInvariant  BY AlwaysEventuallyKnownInvariant
<1>ekl. EKLT(WPrimeStep(am, alpha, p, d))  BY <1>ekinv, <1>wsm, EKExtract
<1>ek. (WPrimeStep(am, alpha, p, d) \subseteq Msgs)
       ~> (\A a \in LiveAcceptors : WPrimeStep(am, alpha, p, d) \subseteq known_messages[a])
  BY <1>ekl DEF EKLT
<1>elimb. [](( \A a \in LiveAcceptors : WPrimeStep(am, alpha, p, d) \subseteq known_messages[a])
             => WPrimeStep(am, alpha, p, d) \subseteq known_messages[s])
  BY <1>elim
<1>eks. (WPrimeStep(am, alpha, p, d) \subseteq Msgs)
        ~> (WPrimeStep(am, alpha, p, d) \subseteq known_messages[s])
  BY <1>ek, <1>elimb, PTL
<1>safeb. [](WPrimeStep(am, alpha, p, d) \subseteq known_messages[s]
             => (\E twoa \in Msgs : Sig(twoa)=s /\ B(twoa)=B(p) /\ HasDepth(alpha,twoa,d+1)))
  BY <1>safe0 DEF TwoASafeConcl
<1> QED  BY <1>eks, <1>safeb, PTL
====================================================================
