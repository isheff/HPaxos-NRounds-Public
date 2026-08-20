-------------------- MODULE AlwaysEventuallyKnownInvariant --------------------
EXTENDS HPaxosPlusCal, EventuallyKnown
LOCAL INSTANCE TLAPS

LEMMA AlwaysEventuallyKnownInvariant ==
  (/\ Spec
   /\ MessageInterfaceAssumptions
   /\ LearnerGraphAssumptions
   /\ AcceptorsAssumptions
   /\ NetworkAssumption
  ) => []EventuallyKnownInvariant
<1> SUFFICES ASSUME Spec, MessageInterfaceAssumptions, LearnerGraphAssumptions, AcceptorsAssumptions, NetworkAssumption
             PROVE []EventuallyKnownInvariant  OBVIOUS
<1>ek. \A m \in SUBSET Messages :
        (m \subseteq RelevantMsgs) ~> (\A a \in LiveAcceptors : m \subseteq known_messages[a])
  BY EventuallyKnown
<1>box. \A m \in SUBSET Messages :
          []((m \subseteq RelevantMsgs) ~> (\A a \in LiveAcceptors : m \subseteq known_messages[a]))
  <2> SUFFICES ASSUME NEW m \in SUBSET Messages
               PROVE []((m \subseteq RelevantMsgs) ~> (\A a \in LiveAcceptors : m \subseteq known_messages[a]))
    OBVIOUS
  <2>1. (m \subseteq RelevantMsgs) ~> (\A a \in LiveAcceptors : m \subseteq known_messages[a])  BY <1>ek
  <2> QED BY <2>1, PTL
<1> QED BY <1>box DEF EventuallyKnownInvariant
====================================================================