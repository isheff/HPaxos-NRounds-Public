--------------------------- MODULE CCandNotSent ---------------------------
\* The record a safe acceptor builds has never been sent before.
\*
\* Suppose it had.  It is signed by s (CForcedSendAgreesAt), so it would be one
\* of s's own sent messages -- an element of CSelfSent(s) -- and CAT(s, x)
\* contains all of those.  But CAT(s, x) is exactly the candidate's own STRICT
\* history, and TranExclusive(m) = Tran(m) \ {m} puts m outside it.
\*
\* No acyclicity argument is needed: the strict history excludes its own
\* message by definition.  This is what makes a well-formed candidate always a
\* REAL send -- Msgs strictly grows -- so the concrete step is never a stutter,
\* which is what ENABLED of the ANGLE-bracket action needs (CSafeStepEnabled).
EXTENDS HPaxosPlusCalConcrete, TLAPS

LEMMA CCandNotSent ==
  ASSUME NEW s, NEW x,
         CForcedSendAgreesAt(s, x),
         CWellFormed(CCand(s, x))
  PROVE  CCand(s, x) \notin Msgs
<1>1. Sig(CCand(s, x)) = s /\ TranExclusive(CCand(s, x)) = CAT(s, x)
  BY DEF CForcedSendAgreesAt
<1> SUFFICES ASSUME CCand(s, x) \in Msgs
             PROVE  FALSE
  OBVIOUS
<1>2. CCand(s, x) \in CSelfSent(s)
  BY <1>1 DEF CSelfSent
<1>3. CCand(s, x) \in CAT(s, x)
  BY <1>2 DEF CAT
<1>4. CCand(s, x) \in TranExclusive(CCand(s, x))
  BY <1>3, <1>1
<1> QED
  BY <1>4 DEF TranExclusive
=============================================================================
