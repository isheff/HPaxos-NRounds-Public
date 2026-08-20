---------------------------- MODULE LearnLeadsTo ----------------------------
\* The WF1 leads-to recipe: each premise is boxed (via BoxAct, the
\* operator-laundering wrapper kept in HPaxosPlusCal) and handed to PTL, which
\* does WF1 natively. Feeding UNBOXED action facts to the final PTL fails.
\*
\* WEAKENED: fairness is only available for the LiveRelevant-restricted
\* action relevant_receive, so the leads-to source carries x \in RelevantMsgs
\* (which also supplies the restricted action's extra enabling conjunct).
EXTENDS HPaxosPlusCal,
        InvHolds, InvStep, RelMono, KnownMono,
        RelevantLearnEnabled, NetworkAssumptionInst
LOCAL INSTANCE TLAPS

\* Single-message learn leads-to (WF1, boxed-premise recipe).
LEMMA LearnLeadsTo ==
  ASSUME AcceptorsAssumptions,
         NEW a \in LiveAcceptors, NEW x \in Messages
  PROVE  Spec /\ NetworkAssumption =>
           ((x \in RelevantMsgs /\ TranExclusive(x) \subseteq known_messages[a])
             ~> (x \in known_messages[a]))
<1>a. a \in SafeAcceptors  BY DEF AcceptorsAssumptions, LiveAcceptorsAssumption
<1> DEFINE P == Inv /\ x \in RelevantMsgs /\ TranExclusive(x) \subseteq known_messages[a]
                    /\ x \notin known_messages[a]
<1> DEFINE Q == x \in known_messages[a]
<1> DEFINE R == x \in RelevantMsgs /\ TranExclusive(x) \subseteq known_messages[a]
<1>inv. Spec => []Inv  BY InvHolds
<1>b1. Spec => BoxAct(P /\ [Next]_vars => (P' \/ Q'))
  <2>1. P /\ [Next]_vars => (P' \/ Q')
    <3>1. Inv /\ [Next]_vars => Inv'  BY InvStep
    <3>2. Inv /\ (x \in RelevantMsgs) /\ [Next]_vars => (x \in RelevantMsgs)'  BY RelMono
    <3>3. Inv /\ [Next]_vars => known_messages[a] \subseteq known_messages'[a]  BY KnownMono, <1>a
    <3> QED  BY <3>1, <3>2, <3>3
  <2> QED  BY <2>1, PTL DEF Spec, BoxAct
<1>b2. Spec => BoxAct(P /\ <<Next /\ relevant_receive(<<a, x>>)>>_vars => Q')
  <2>1. P /\ <<Next /\ relevant_receive(<<a, x>>)>>_vars => Q'
    BY <1>a DEF relevant_receive, safe_acceptor_receives_message, Inv
  <2> QED  BY <2>1, PTL DEF Spec, BoxAct
<1>b3. Spec => [](P => ENABLED <<relevant_receive(<<a, x>>)>>_vars)
  <2>1. P => ENABLED <<relevant_receive(<<a, x>>)>>_vars
    BY <1>a, RelevantLearnEnabled DEF Inv, RelevantMsgs
  <2> QED  BY <2>1, PTL DEF Spec
<1>axmem. <<a, x>> \in LiveAcceptors \times Messages  OBVIOUS
<1>w. Spec /\ NetworkAssumption => WF_vars(relevant_receive(<<a, x>>))
  <2>1. NetworkAssumption => WF_vars(relevant_receive(<<a, x>>))
    BY <1>axmem, NetworkAssumptionInst
  <2> QED  BY <2>1
<1>n. Spec => [][Next]_vars  BY DEF Spec
<1>pq. Spec /\ NetworkAssumption => (P ~> Q)  BY <1>b1, <1>b2, <1>b3, <1>w, <1>n, PTL DEF BoxAct
<1>ri. Spec => [](R => (P \/ Q))
  <2>1. Inv /\ R => (P \/ Q)  OBVIOUS
  <2>2. Spec => [](Inv /\ R => (P \/ Q))  BY <2>1, PTL DEF Spec
  <2> QED  BY <2>2, <1>inv, PTL
<1> QED  BY <1>pq, <1>ri, PTL
====================================================================
