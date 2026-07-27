----------------------------- MODULE DepthBridge -----------------------------
EXTENDS HPaxosPlusCal, ExDiaBarcanFlex, NetSubMsgElem
LOCAL INSTANCE TLAPS

LEMMA DepthBridge ==
  ASSUME NEW a, NEW alpha, NEW p, NEW dd, NEW allmessages
  PROVE  Spec =>
         (IsAllMessagesEverSent(allmessages)
          => ((<>(\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd)))
              => (\E y \in allmessages : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))))
<1>c1. Init => ((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))
                <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd)))
  OBVIOUS
<1>c2. ((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))
        <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))) /\ [Next]_vars
       => ((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))
           <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd)))'
  OBVIOUS
<1>eb0. Spec => []((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))
                   <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd)))
  BY <1>c1, <1>c2, PTL DEF Spec
<1> SUFFICES ASSUME Spec, IsAllMessagesEverSent(allmessages),
                    <>(\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))
             PROVE  \E y \in allmessages : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd)
  OBVIOUS
<1>eb. []((\E y \in Msgs : Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))
          <=> (\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd)))  BY <1>eb0
<1>u. <>(\E y : y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))  BY <1>eb, PTL
<1>2. \E y : <>(y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))
  BY <1>u, ExDiaBarcanFlex
<1> SUFFICES ASSUME NEW y, <>(y \in Msgs /\ Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))
             PROVE  \E z \in allmessages : Sig(z)=a /\ B(z)=B(p) /\ HasDepth(alpha,z,dd)
  BY <1>2
<1>rigP. [](Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd))
         \/ []( ~(Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd)))  OBVIOUS
<1>rigM. [](y \in Messages) \/ []( ~(y \in Messages))  OBVIOUS
<1>nm. [](y \in Msgs => y \in Messages)  BY NetSubMsgElem
<1>P. Sig(y)=a /\ B(y)=B(p) /\ HasDepth(alpha,y,dd)  BY <1>rigP, PTL
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
