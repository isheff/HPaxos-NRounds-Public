----------------------------- MODULE CTranAcyclic -----------------------------
EXTENDS MessageConcrete, CFields, CTranResolve, CMessagesSubMC,
        CMessageTranClosed, CMCAcyclic

LEMMA CTranAcyclic == ASSUME MessageInterface = CMI PROVE TranAcyclic
<1> SUFFICES ASSUME NEW m \in Messages, NEW x \in TranExclusive(m) PROVE m \notin Tran(x)
  BY DEF TranAcyclic
<1>1. Messages = CMessages  BY CFields
<1>2. m \in CMessages  BY <1>1
<1>3. Tran(m) = CTran(m)  BY <1>2, CTranResolve
<1>4. TranExclusive(m) = CTranExcl(m)  BY <1>3 DEF TranExclusive, CTranExcl
<1>5. x \in CTranExcl(m)  BY <1>4
<1>6. m \in CMC  BY <1>2, CMessagesSubMC
<1>7. x \in CTran(m)  BY <1>5 DEF CTranExcl
<1>8. x \in CMessages  BY <1>2, <1>7, CMessageTranClosed
<1>9. Tran(x) = CTran(x)  BY <1>8, CTranResolve
<1>10. ~(m \in CTran(x))  BY <1>6, <1>5, CMCAcyclic
<1> QED BY <1>9, <1>10
=============================================================================
