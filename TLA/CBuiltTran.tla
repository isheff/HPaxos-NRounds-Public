--------------------------- MODULE CBuiltTran ---------------------------
\* The built record's history is the Tran-closure of its priors, and it is not
\* itself in that closure.  The second part is a LEVEL argument, not an
\* acyclicity one: CPriorsDecreasesLevel puts the record strictly above each
\* prior, and CTranLevelLE puts everything in a prior's history at or below it.
EXTENDS HPaxosPlusCalConcrete, CBuiltInCMC, CTranRec, CMessagesSubMC,
        CPriorsDecreasesLevel, CTranLevelLE, CMinLevelDom, TLAPS

LEMMA CBuiltTran ==
  ASSUME NEW sdr \in CSenders, NEW pl \in CPayload,
         NEW pr, pr \subseteq CMessages, IsFiniteSet(pr)
  PROVE  LET cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
         IN  /\ CTran(cand) = {cand} \cup UNION {CTran(p) : p \in pr}
             /\ CTranExcl(cand) = UNION {CTran(p) : p \in pr}
<1> DEFINE cand == [sender |-> sdr, payload |-> pl, priors |-> pr]
<1>mc. cand \in CMC
  BY CBuiltInCMC
<1>pri. CPriors(cand) = pr
  BY DEF CPriors
<1>1. CTran(cand) = {cand} \cup UNION {CTran(p) : p \in pr}
  BY <1>mc, <1>pri, CTranRec
<1>2. cand \notin UNION {CTran(p) : p \in pr}
  <2> SUFFICES ASSUME NEW p \in pr, cand \in CTran(p)
               PROVE  FALSE
    OBVIOUS
  <2>1. p \in CMC
    BY CMessagesSubMC
  <2>2. p \in CPriors(cand)
    BY <1>pri
  <2>3. CMinLevel(p) < CMinLevel(cand)
    BY <1>mc, <2>2, CPriorsDecreasesLevel
  <2>4. CTranBelowProp(p)
    BY <2>1, CTranLevelLE
  <2>5. CMinLevel(cand) <= CMinLevel(p)
    BY <2>4 DEF CTranBelowProp
  <2>6. CMinLevel(p) \in Nat /\ CMinLevel(cand) \in Nat
    BY <1>mc, <2>1, CMinLevelDom
  <2> QED
    BY <2>3, <2>5, <2>6
<1>3. CTranExcl(cand) = UNION {CTran(p) : p \in pr}
  BY <1>1, <1>2 DEF CTranExcl
<1> QED
  BY <1>1, <1>3
=============================================================================
