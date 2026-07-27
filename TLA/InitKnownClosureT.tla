-------------------------- MODULE InitKnownClosureT --------------------------
EXTENDS HPaxosPlusCal

LEMMA InitKnownClosureT == Init => KnownTranClosureInvT
<1> SUFFICES ASSUME Init PROVE KnownTranClosureInvT  OBVIOUS
<1>1. known_messages = [s \in SafeAcceptors |-> {}]  BY DEF Init
<1> SUFFICES ASSUME NEW s \in SafeAcceptors PROVE TranClosure(known_messages[s]) = known_messages[s]
  BY DEF KnownTranClosureInvT
<1>2. known_messages[s] = {}  BY <1>1
<1>3. TranClosure({}) = {}  BY DEF TranClosure
<1> QED BY <1>2, <1>3
====================================================================
