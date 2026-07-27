--------------------------- MODULE CAlwaysAProposal ---------------------------
EXTENDS MessageConcrete, CFields, CTranResolve, CMessagesSubMC,
        CSelfInTran, CMessageTranClosed

LEMMA CAlwaysAProposal == ASSUME MessageInterface = CMI PROVE AlwaysAProposal
<1> SUFFICES ASSUME NEW m \in Messages PROVE GetProposals(m) # {}  BY DEF AlwaysAProposal
<1>1. Messages = CMessages  BY CFields
<1>2. m \in CMessages  BY <1>1
<1>3. Tran(m) = CTran(m)  BY <1>2, CTranResolve
<1>4. m \in CMC  BY <1>2, CMessagesSubMC
<1>5. \A x \in CTran(m) : CWellFormed(x)  BY <1>2 DEF CMessages
<1>6. m \in CTran(m)  BY <1>4, CSelfInTran
<1>7. CWellFormed(m)  BY <1>5, <1>6
<1>8. \E a \in CTran(m) : CIsProposal(a)  BY <1>7 DEF CWellFormed
<1> PICK a \in CTran(m) : CIsProposal(a)  BY <1>8
<1>9. a \in CMessages  BY <1>2, CMessageTranClosed
<1>10. a \in CProposals  BY <1>9 DEF CProposals
<1>11. Proposals = CProposals  BY CFields
<1>12. a \in Proposals  BY <1>10, <1>11
<1>13. a \in Tran(m)  BY <1>3
<1>14. a \in Proposals \cap Tran(m)  BY <1>12, <1>13
<1> QED BY <1>14 DEF GetProposals
=============================================================================
