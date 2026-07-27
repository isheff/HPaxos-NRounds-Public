----------------------------- MODULE CTranResolve -----------------------------
EXTENDS MessageConcrete, CMessagesSubMC, CTranReflexiveSplit

LEMMA CTranResolve == ASSUME MessageInterface = CMI, NEW m \in CMessages
  PROVE Tran(m) = CTran(m)
<1>1. Tran(m) = {m} \cup MessageInterface.tran[m]  BY DEF Tran
<1>2. MessageInterface.tran[m] = CTranExcl(m)  BY DEF CMI, CTranField
<1>3. Tran(m) = {m} \cup CTranExcl(m)  BY <1>1, <1>2
<1>4. m \in CMC  BY CMessagesSubMC
<1>5. CTran(m) = {m} \cup CTranExcl(m)  BY <1>4, CTranReflexiveSplit
<1> QED BY <1>3, <1>5
=============================================================================
