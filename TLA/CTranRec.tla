------------------------------- MODULE CTranRec -------------------------------
EXTENDS MessageConcrete, CPriorsInMC, CPriorsDecreasesLevel, CRecursiveFuncRec

LEMMA CTranRec == ASSUME NEW m \in CMC
  PROVE CTran(m) = {m} \cup UNION {CTran(p) : p \in CPriors(m)}
<1>1. \A xx \in CMC : CPriors(xx) \subseteq CMC  BY CPriorsInMC
<1>2. \A xx \in CMC : \A yy \in CPriors(xx) : CMinLevel(yy) < CMinLevel(xx)
  BY CPriorsDecreasesLevel
<1>3. CRecursiveFunc(CTranR, CPriors, m)
        = CTranR(m, {CRecursiveFunc(CTranR, CPriors, p) : p \in CPriors(m)})
  BY <1>1, <1>2, CRecursiveFuncRec
<1> QED BY <1>3 DEF CTran, CTranR
=============================================================================
