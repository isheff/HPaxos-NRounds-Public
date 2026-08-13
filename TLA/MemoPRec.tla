------------------------------- MODULE MemoPRec -------------------------------
\* The priors-recursive memo unfolds one level: MemoP(m) is the MemoR assembly
\* over the MemoP records of m's own priors.  Mirrors CTranRec / CCflRec.
EXTENDS WellFormedRecDef, CRecursiveFuncRec, CPriorsInMC,
        CPriorsDecreasesLevel
LOCAL INSTANCE TLAPS

LEMMA MemoPRec == ASSUME NEW m \in CMC
  PROVE MemoP(m) = MemoR(m, {MemoP(p) : p \in CPriors(m)})
<1>1. \A x \in CMC : CPriors(x) \subseteq CMC  BY CPriorsInMC
<1>2. \A x \in CMC : \A y \in CPriors(x) : CMinLevel(y) < CMinLevel(x)
  BY CPriorsDecreasesLevel
<1>3. CRecursiveFunc(MemoR, CPriors, m)
        = MemoR(m, {CRecursiveFunc(MemoR, CPriors, p) : p \in CPriors(m)})
  BY <1>1, <1>2, CRecursiveFuncRec
<1> QED BY <1>3 DEF MemoP
=============================================================================
