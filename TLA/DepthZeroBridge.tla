--------------------------- MODULE DepthZeroBridge ---------------------------
EXTENDS HPaxosPlusCal, ExDiaBarcanFlex, NetSubMsgElem
LOCAL INSTANCE TLAPS

\* Specialized bridge for the concrete depth-0 predicate.  Parameters a, alpha,
\* p, allmessages are all FIRST-ORDER (constants), so -- unlike the generic
\* P-parameterized DiamondExistsBridge -- this IS citable at concrete arguments.
LEMMA DepthZeroBridge ==
  ASSUME NEW a, NEW alpha, NEW p, NEW allmessages
  PROVE  Spec =>
         (IsAllMessagesEverSent(allmessages)
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
<1> SUFFICES ASSUME Spec, IsAllMessagesEverSent(allmessages),
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
<1>rigM. [](y \in Messages) \/ []( ~(y \in Messages))  OBVIOUS
<1>nm. [](y \in Msgs => y \in Messages)  BY NetSubMsgElem
<1>P. Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,0)  BY <1>rigP, PTL
<1>dn. <>(y \in Msgs)  BY PTL
<1>M. y \in Messages  BY <1>dn, <1>nm, <1>rigM, PTL
<1>am. y \in allmessages
  <2>1. \A mm : (mm \in allmessages <=> IAMESCond(mm))  BY DEF IsAllMessagesEverSent
  <2> HIDE DEF IAMESCond
  <2>2. y \in allmessages <=> IAMESCond(y)  BY <2>1
  <2>3. IAMESCond(y)  BY <1>M, <1>dn DEF IAMESCond
  <2> QED  BY <2>2, <2>3
<1> QED  BY <1>am, <1>P
====================================================================
