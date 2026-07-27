------------------------------ MODULE InitInv ------------------------------
\* FiniteSetTheorems supplies FS_EmptySet. It shares FiniteSets with
\* HPaxosPlusCal (via MessageInterface), so both must be EXTENDS.
EXTENDS HPaxosPlusCal, FiniteSetTheorems

LEMMA InitInv == Init => Inv
<1> SUFFICES ASSUME Init PROVE Inv  OBVIOUS
<1>1. Msgs = {} /\ known_messages = [s \in SafeAcceptors |-> {}]  BY DEF Init
<1>2. IsFiniteSet(Msgs)  BY <1>1, FS_EmptySet
<1> QED  BY <1>1, <1>2 DEF Inv
====================================================================
