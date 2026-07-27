---------------------------- MODULE CTranTransProof ----------------------------
EXTENDS MessageConcrete, CFields, CTranResolve, CMessagesSubMC,
        CMessageTranClosed, CTranTrans

LEMMA CTranTransProof == ASSUME MessageInterface = CMI PROVE TranTrans
<1> SUFFICES ASSUME NEW m \in Messages, NEW x \in Tran(m) PROVE Tran(x) \subseteq Tran(m)
  BY DEF TranTrans
<1>1. Messages = CMessages  BY CFields
<1>2. m \in CMessages  BY <1>1
<1>3. Tran(m) = CTran(m)  BY <1>2, CTranResolve
<1>4. x \in CTran(m)  BY <1>3
<1>5. m \in CMC  BY <1>2, CMessagesSubMC
<1>6. x \in CMessages  BY <1>2, <1>4, CMessageTranClosed
<1>7. Tran(x) = CTran(x)  BY <1>6, CTranResolve
<1>8. CTran(x) \subseteq CTran(m)  BY <1>5, <1>4, CTranTrans
<1> QED BY <1>3, <1>7, <1>8
=============================================================================
