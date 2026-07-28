--------------------------- MODULE CAgreesFromJoint ---------------------------
\* The joint invariant discharges the forced-send agreement at every guarded
\* pair.  This is where the four hypotheses of CForcedSendAgreesFromInvariant
\* are supplied: CRMIsMax gives the antichain identity, CTranClosureOfMax gives
\* the closure identity, and CUpGood gives the typing and finiteness.
EXTENDS HPaxosPlusCalConcrete, CUpGood, CRMIsMax, CTranClosureOfMax,
        CForcedSendAgreesFromInvariant, FiniteSetTheorems, TLAPS

LEMMA CAgreesFromJoint ==
  ASSUME ConcreteMessageInterface, SafeAcceptorsAssumption, CJoint
  PROVE  \A s \in SafeAcceptors : \A x \in Messages :
           (x \in Msgs /\ TranExclusive(x) \subseteq known_messages[s])
             => CForcedSendAgreesAt(s, x)
<1> SUFFICES ASSUME NEW s \in SafeAcceptors, NEW x \in Messages,
                    x \in Msgs, TranExclusive(x) \subseteq known_messages[s]
             PROVE  CForcedSendAgreesAt(s, x)
  OBVIOUS
<1>inv. CInv /\ KnownTranClosureInvT /\ SelfSentBoundedInvT /\ CRecentIsMax
  BY DEF CJoint
<1> DEFINE Up == (known_messages[s] \cup {x}) \cup CSelfSent(s)
<1>at. CAT(s, x) = Up
  BY DEF CAT
<1>up. /\ Up \subseteq Messages
       /\ IsFiniteSet(Up)
       /\ \A z \in Up : Tran(z) \subseteq Up
       /\ Up \subseteq Msgs
  BY <1>inv, CUpGood
<1>rm. CRM(s, x) = CMMax(Up)
  BY <1>inv, CRMIsMax
<1>sub. CRM(s, x) \subseteq Msgs
  BY <1>rm, <1>up DEF CMMax
<1>fin. IsFiniteSet(CRM(s, x))
  BY <1>sub, <1>inv, FS_Subset DEF CInv
<1>cl. TranClosure(CRM(s, x)) = Up
  BY <1>rm, <1>up, CTranClosureOfMax
<1>msgs. Msgs \subseteq Messages
  BY <1>inv DEF CInv
<1> QED
  BY <1>at, <1>sub, <1>fin, <1>cl, <1>rm, <1>msgs, CForcedSendAgreesFromInvariant
=============================================================================
