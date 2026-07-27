--------------------------- MODULE NeverCaughtStep ---------------------------
EXTENDS HPaxosPlusCal
LOCAL INSTANCE TLAPS

\* Whenever the two forking same-signer witnesses are both in Msgs, their
\* signer is caught in Msgs.  Phrased over the single atom {m1,m2} \subseteq
\* Msgs (FiniteDiamond's target).  INV1 with Spec in the GOAL.
LEMMA NeverCaughtStep ==
  ASSUME NEW s, s \in Acceptors, NEW m1, NEW m2,
         Sig(m1)=s, Sig(m2)=s, m1 \notin Tran(m2), m2 \notin Tran(m1)
  PROVE  Spec => []({m1, m2} \subseteq Msgs => s \in CaughtS(Msgs))
<1>1. Init => ({m1, m2} \subseteq Msgs => s \in CaughtS(Msgs))
  <2> SUFFICES ASSUME Init, {m1, m2} \subseteq Msgs PROVE s \in CaughtS(Msgs)  OBVIOUS
  <2>1. m1 \in Msgs /\ m2 \in Msgs  OBVIOUS
  <2> QED  BY <2>1 DEF CaughtS
<1>2. ({m1, m2} \subseteq Msgs => s \in CaughtS(Msgs)) /\ [Next]_vars
        => ({m1, m2} \subseteq Msgs => s \in CaughtS(Msgs))'
  <2> SUFFICES ASSUME ({m1, m2} \subseteq Msgs)' PROVE (s \in CaughtS(Msgs))'  OBVIOUS
  <2>1. (m1 \in Msgs /\ m2 \in Msgs)'  OBVIOUS
  <2> QED  BY <2>1 DEF CaughtS
<1> QED  BY <1>1, <1>2, PTL DEF Spec
====================================================================
