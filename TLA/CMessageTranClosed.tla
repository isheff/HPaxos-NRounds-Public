-------------------------- MODULE CMessageTranClosed --------------------------
EXTENDS MessageConcrete, CTranLevelLE, CTranTrans

LEMMA CMessageTranClosed ==
 ASSUME NEW m \in CMessages
 PROVE CTran(m) \subseteq CMessages
<1>0. m \in CMC /\ (\A x \in CTran(m) : CWellFormed(x))  BY DEF CMessages
<1> SUFFICES ASSUME NEW y \in CTran(m) PROVE y \in CMessages  OBVIOUS
<1>1. y \in CMC  BY <1>0, CTranLevelLE DEF CTranBelowProp
<1>2. CTran(y) \subseteq CTran(m)  BY <1>0, CTranTrans
<1>3. \A z \in CTran(y) : CWellFormed(z)  BY <1>0, <1>2
<1> QED BY <1>1, <1>3 DEF CMessages
=============================================================================
