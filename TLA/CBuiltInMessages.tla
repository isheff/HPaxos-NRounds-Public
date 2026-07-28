--------------------------- MODULE CBuiltInMessages ---------------------------
\* Everything strictly below the built record is already well formed -- it lies
\* in CMessages -- so CWellFormed of the record alone decides its membership.
EXTENDS HPaxosPlusCalConcrete, CBuiltInCMC, CBuiltTran, CSelfInTran, TLAPS

LEMMA CBuiltInMessages ==
  ASSUME NEW sdr \in CSenders, NEW pl \in CPayload,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr)
  PROVE  LET cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
         IN  cand \in CMessages <=> CWellFormed(cand)
<1> DEFINE cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
<1>mc. cand \in CMC
  BY CBuiltInCMC
<1>tr. CTran(cand) = {cand} \cup UNION {CTran(p) : p \in pr}
  BY CBuiltTran
<1>1. \A z \in UNION {CTran(p) : p \in pr} : CWellFormed(z)
  <2> SUFFICES ASSUME NEW p \in pr, NEW z \in CTran(p)
               PROVE  CWellFormed(z)
    OBVIOUS
  <2>1. p \in CMessages
    OBVIOUS
  <2> QED
    BY <2>1 DEF CMessages
<1>2. CASE CWellFormed(cand)
  <2>1. \A z \in CTran(cand) : CWellFormed(z)
    BY <1>tr, <1>1, <1>2
  <2>2. cand \in CMessages
    BY <1>mc, <2>1 DEF CMessages
  <2> QED
    BY <1>2, <2>2
<1>3. CASE cand \in CMessages
  <2>1. cand \in CTran(cand)
    BY <1>mc, CSelfInTran
  <2> QED
    BY <2>1, <1>3 DEF CMessages
<1> QED
  BY <1>2, <1>3
=============================================================================
