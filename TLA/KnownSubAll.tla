----------------------------- MODULE KnownSubAll -----------------------------
EXTENDS HPaxosPlusCal, InvHolds
LOCAL INSTANCE TLAPS

\* Whatever a LIVE acceptor knows is in the ever-known set -- almost by
\* definition (no fairness needed): current knowledge witnesses <>KnownToLive.
LEMMA KnownSubAll ==
  ASSUME AcceptorsAssumptions, NEW s \in LiveAcceptors, NEW am
  PROVE  Spec => (IsAllMessagesEverKnown(am) => KnownAllBoxOp(s, am))
<1>ssafe. s \in SafeAcceptors  BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
<1>pe. \A xx : Spec => (IsAllMessagesEverKnown(am) => [](xx \in known_messages[s] => xx \in am))
  <2> SUFFICES ASSUME NEW xx
               PROVE Spec => (IsAllMessagesEverKnown(am) => [](xx \in known_messages[s] => xx \in am))
    OBVIOUS
  <2>kb. Spec => [](xx \in known_messages[s] => KnownToLive(xx))
    <3>1. Init => (xx \in known_messages[s] => KnownToLive(xx))  BY DEF KnownToLive
    <3>2. (xx \in known_messages[s] => KnownToLive(xx)) /\ [Next]_vars
            => (xx \in known_messages[s] => KnownToLive(xx))'  BY DEF KnownToLive
    <3> QED  BY <3>1, <3>2, PTL DEF Spec
  <2>mb. Spec => [](xx \in known_messages[s] => xx \in Messages)
    <3>1. Inv /\ xx \in known_messages[s] => xx \in Messages  BY <1>ssafe DEF Inv
    <3>2. Spec => []Inv  BY InvHolds
    <3> QED  BY <3>1, <3>2, PTL DEF Spec
  <2>rigM. [](xx \in Messages) \/ []( ~(xx \in Messages))  OBVIOUS
  <2>rigA. [](xx \in am) \/ []( ~(xx \in am))  OBVIOUS
  <2> SUFFICES ASSUME Spec, IsAllMessagesEverKnown(am)
               PROVE [](xx \in known_messages[s] => xx \in am)  OBVIOUS
  <2>kbb. [](xx \in known_messages[s] => KnownToLive(xx))  BY <2>kb
  <2>mbb. [](xx \in known_messages[s] => xx \in Messages)  BY <2>mb
  <2>equiv. xx \in am <=> (xx \in Messages /\ <>KnownToLive(xx))
    <3>1. \A mm : (mm \in am <=> IAMEKCond(mm))  BY DEF IsAllMessagesEverKnown
    <3> HIDE DEF IAMEKCond
    <3>2. xx \in am <=> IAMEKCond(xx)  BY <3>1
    <3> QED  BY <3>2 DEF IAMEKCond
  <2> QED  BY <2>kbb, <2>mbb, <2>equiv, <2>rigM, <2>rigA, PTL
<1> SUFFICES ASSUME Spec, IsAllMessagesEverKnown(am) PROVE KnownAllBoxOp(s, am)  OBVIOUS
<1>per. \A xx : [](xx \in known_messages[s] => xx \in am)  BY <1>pe
<1>ba. (\A xx : [](xx \in known_messages[s] => xx \in am))
       <=> ([](\A xx : xx \in known_messages[s] => xx \in am))  OBVIOUS
<1> QED  BY <1>per, <1>ba DEF KnownAllBoxOp
====================================================================
