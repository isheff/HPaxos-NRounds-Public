----------------------------- MODULE CRefsResolve -----------------------------
EXTENDS MessageConcrete, CTranResolve, CMessageTranClosed

LEMMA CRefsResolve == ASSUME MessageInterface = CMI, NEW m \in CMessages
  PROVE Refs(m) = CRefs(m)
<1>1. Tran(m) = CTran(m)  BY CTranResolve
<1>2. TranExclusive(m) = CTranExcl(m)  BY <1>1 DEF TranExclusive, CTranExcl
<1>3. \A y \in CTranExcl(m) : y \in CMessages
  <2> SUFFICES ASSUME NEW y \in CTranExcl(m) PROVE y \in CMessages  OBVIOUS
  <2>1. y \in CTran(m)  BY DEF CTranExcl
  <2> QED BY <2>1, CMessageTranClosed
<1>4. \A y \in CTranExcl(m) : Tran(y) = CTran(y)  BY <1>3, CTranResolve
<1>5. \A x \in CTranExcl(m) : \A y \in CTranExcl(m) :
        x \notin TranExclusive(y) <=> (y = x \/ x \notin CTran(y))
  BY <1>4 DEF TranExclusive
<1> QED BY <1>2, <1>5 DEF Refs, CRefs
=============================================================================
