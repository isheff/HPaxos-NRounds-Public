--------------------------- MODULE DepthZeroBridge ---------------------------
EXTENDS HPaxosPlusCal, ExDiaBarcanFlex, NetSubMsgElem, LiveSigRelElem, AllMsgRelElem
LOCAL INSTANCE TLAPS

\* Specialized bridge for the concrete depth predicate, ever-known flavour:
\* the extracted witness y is signed by the LIVE acceptor a, so it is
\* live-relevant once sent (LiveSigRelElem) and hence eventually known
\* (AllMsgRelElem, under the weakened fairness) -- i.e. in allmessages.
\* Parameters are all FIRST-ORDER, so this IS citable at concrete arguments.
LEMMA DepthZeroBridge ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         NEW a \in LiveAcceptors, NEW alpha, NEW p, NEW allmessages
  PROVE  (Spec /\ NetworkAssumption) =>
         (IsAllMessagesEverKnown(allmessages)
          => ((<>(\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)))
              => (\E y \in allmessages : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))))
<1>c1. Init => ((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
                <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)))
  OBVIOUS
<1>c2. ((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
        <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))) /\ [Next]_vars
       => ((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
           <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)))'
  OBVIOUS
<1>eb0. Spec => []((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
                   <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)))
  BY <1>c1, <1>c2, PTL DEF Spec
<1> SUFFICES ASSUME Spec, NetworkAssumption, IsAllMessagesEverKnown(allmessages),
                    <>(\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
             PROVE  \E y \in allmessages : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)
  OBVIOUS
<1>eb. []((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
          <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)))  BY <1>eb0
<1>u. <>(\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))  BY <1>eb, PTL
<1>2. \E y : <>(y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
  BY <1>u, ExDiaBarcanFlex
<1> SUFFICES ASSUME NEW y, <>(y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
             PROVE  \E z \in allmessages : Sig(z)=a /\ B(z)=B(p) /\ HasDepth(alpha,z,0)
  BY <1>2
<1>rigP. [](Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0))
         \/ []( ~(Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)))  OBVIOUS
<1>rigAM. [](y \in allmessages) \/ []( ~(y \in allmessages))  OBVIOUS
<1>P. Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)  BY <1>rigP, PTL
<1>dn. <>(y \in Msgs)  BY PTL
<1>sigl. Sig(y) \in LiveAcceptors  BY <1>P
<1>rel. [](y \in Msgs => y \in RelevantMsgs)
  <2>1. Spec => [](y \in Msgs => y \in RelevantMsgs)  BY <1>sigl, LiveSigRelElem
  <2> QED  BY <2>1
<1>ram. [](y \in RelevantMsgs => y \in allmessages)
  <2>1. (Spec /\ NetworkAssumption)
          => (IsAllMessagesEverKnown(allmessages) => RelAllBoxOp(y, allmessages))
    BY AllMsgRelElem
  <2> QED  BY <2>1 DEF RelAllBoxOp
<1>am. y \in allmessages  BY <1>dn, <1>rel, <1>ram, <1>rigAM, PTL
<1> QED  BY <1>am, <1>P
====================================================================
