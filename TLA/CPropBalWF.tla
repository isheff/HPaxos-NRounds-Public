------------------------------ MODULE CPropBalWF ------------------------------
\* A proposal that is a real message carries its own CB in its ballot field
\* (CFilterOut's first clause, read off its own well-formedness).
EXTENDS MessageConcrete, CMessagesSubMC, CSelfInTran, TLAPS

LEMMA CPropBalWF ==
  ASSUME NEW w \in CMessages, CIsProposal(w)
  PROVE CB(w) = w.payload.ballot
<1>1. w \in CMC  BY CMessagesSubMC
<1>2. w \in CTran(w)  BY <1>1, CSelfInTran
<1>3. CWellFormed(w)  BY <1>2 DEF CMessages
<1> QED BY <1>3 DEF CWellFormed, CFilterOut
=============================================================================
