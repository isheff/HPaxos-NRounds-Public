------------------------------- MODULE AmNowBox -------------------------------
EXTENDS HPaxosPlusCal, AllMsgRelElem
LOCAL INSTANCE TLAPS

\* Ever-known flavour: every LIVE-RELEVANT sent message is in allmessages
\* (needs the weakened fairness -- a live-relevant message is only
\* *eventually* known).
LEMMA AmNowBox ==
  ASSUME MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions,
         LiveAcceptors # {}, NEW allmessages
  PROVE  (Spec /\ NetworkAssumption)
           => (IsAllMessagesEverKnown(allmessages) => []AmNowT(allmessages))
<1>pe. \A xx : (Spec /\ NetworkAssumption)
               => (IsAllMessagesEverKnown(allmessages)
                   => [](xx \in RelevantMsgs => xx \in allmessages))
  <2> SUFFICES ASSUME NEW xx
               PROVE (Spec /\ NetworkAssumption)
                     => (IsAllMessagesEverKnown(allmessages)
                         => [](xx \in RelevantMsgs => xx \in allmessages))
    OBVIOUS
  <2>1. (Spec /\ NetworkAssumption)
          => (IsAllMessagesEverKnown(allmessages) => RelAllBoxOp(xx, allmessages))
    BY AllMsgRelElem
  <2> QED  BY <2>1 DEF RelAllBoxOp
<1> SUFFICES ASSUME Spec, NetworkAssumption, IsAllMessagesEverKnown(allmessages)
             PROVE []AmNowT(allmessages)  OBVIOUS
<1>peb. \A xx : [](xx \in RelevantMsgs => xx \in allmessages)  BY <1>pe
<1>ba. (\A xx : [](xx \in RelevantMsgs => xx \in allmessages))
       <=> ([](\A xx : xx \in RelevantMsgs => xx \in allmessages))  OBVIOUS
<1>rhs. [](\A xx : xx \in RelevantMsgs => xx \in allmessages)  BY <1>peb, <1>ba
<1> QED  BY <1>rhs DEF AmNowT
====================================================================
