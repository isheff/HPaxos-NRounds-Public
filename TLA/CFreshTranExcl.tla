----------------------------- MODULE CFreshTranExcl -----------------------------
EXTENDS MessageConcrete, CTranRec, CPriorsInMC, CPriorsDecreasesLevel,
        CTranLevelLE, CMinLevelDom

\* If a freshly-built record's priors are exactly some finite S \subseteq CMC,
\* its CTranExcl is exactly UNION of S's Trans.
LEMMA CFreshTranExcl ==
  ASSUME NEW rec \in CMC, NEW S, rec.priors = S
  PROVE CTranExcl(rec) = UNION {CTran(q) : q \in S}
<1>1. CTran(rec) = {rec} \cup UNION {CTran(p) : p \in CPriors(rec)}  BY CTranRec
<1>2. CPriors(rec) = S  BY DEF CPriors
<1>3. CTran(rec) = {rec} \cup UNION {CTran(p) : p \in S}  BY <1>1, <1>2
<1>4. rec \notin UNION {CTran(p) : p \in S}
  <2> SUFFICES ASSUME rec \in UNION {CTran(p) : p \in S} PROVE FALSE  OBVIOUS
  <2>1. PICK p \in S : rec \in CTran(p)  OBVIOUS
  <2>Sub. CPriors(rec) \subseteq CMC  BY CPriorsInMC
  <2>2. p \in CMC  BY <2>1, <1>2, <2>Sub
  <2>3. CMinLevel(p) < CMinLevel(rec)  BY <1>2, CPriorsDecreasesLevel
  <2>4. rec \in CMC /\ CMinLevel(rec) <= CMinLevel(p)  BY <2>1, <2>2, CTranLevelLE DEF CTranBelowProp
  <2>5. CMinLevel(p) \in Nat /\ CMinLevel(rec) \in Nat  BY <2>2, CMinLevelDom
  <2> QED BY <2>3, <2>4, <2>5
<1> QED BY <1>3, <1>4 DEF CTranExcl
=============================================================================
