---------------------------- MODULE CTranExclRec ----------------------------
\* The strict closure of ANY CMC record decomposes over its priors -- no
\* well-formedness needed: the record itself cannot occur below a prior
\* (levels strictly decrease), so peeling {m} off CTranRec is exact.  Also:
\* every prior lies in the strict closure.
EXTENDS MessageConcrete, CTranRec, CPriorsInMC, CPriorsDecreasesLevel,
        CTranLevelLE, CMinLevelDom, CSelfInTran
LOCAL INSTANCE TLAPS

LEMMA CTranExclRec ==
  ASSUME NEW m \in CMC
  PROVE /\ CPriors(m) \subseteq CTranExcl(m)
        /\ CTranExcl(m) = UNION {CTran(p) : p \in CPriors(m)}
<1>pmc. \A w \in CMC : CPriors(w) \subseteq CMC  BY CPriorsInMC
<1>tr. CTran(m) = {m} \cup UNION {CTran(p) : p \in CPriors(m)}  BY CTranRec
<1>nx. m \notin UNION {CTran(p) : p \in CPriors(m)}
  <2> SUFFICES ASSUME NEW p \in CPriors(m), m \in CTran(p) PROVE FALSE
    OBVIOUS
  <2>1. p \in CMC  BY <1>pmc
  <2>2. CMinLevel(p) < CMinLevel(m)  BY CPriorsDecreasesLevel
  <2>3. CTranBelowProp(p)  BY <2>1, CTranLevelLE
  <2>4. CMinLevel(m) <= CMinLevel(p)  BY <2>3 DEF CTranBelowProp
  <2>5. CMinLevel(p) \in Nat /\ CMinLevel(m) \in Nat
    BY <2>1, CMinLevelDom
  <2> QED BY <2>2, <2>4, <2>5
<1>te. CTranExcl(m) = UNION {CTran(p) : p \in CPriors(m)}
  BY <1>tr, <1>nx DEF CTranExcl
<1>ps. CPriors(m) \subseteq CTranExcl(m)
  <2> SUFFICES ASSUME NEW p \in CPriors(m) PROVE p \in CTranExcl(m)  OBVIOUS
  <2>1. p \in CMC  BY <1>pmc
  <2>2. p \in CTran(p)  BY <2>1, CSelfInTran
  <2>3. p \in UNION {CTran(q) : q \in CPriors(m)}  BY <2>2
  <2> QED BY <2>3, <1>te
<1> QED BY <1>ps, <1>te
=============================================================================
