-------------------------------- MODULE CCflRec --------------------------------
EXTENDS MessageConcrete, CTranLevelLE, CTranExclDecreasesLevel, CRecursiveFuncRec

\* CCfl unfolding (mirrors CTranRec, via the generic CRecursiveFuncRec).
LEMMA CCflRec == ASSUME NEW m \in CMC
  PROVE CCfl(m) = CCflR(m, {CCfl(y) : y \in CTranExcl(m)})
<1>1. \A x \in CMC : CTranExcl(x) \subseteq CMC
  <2> SUFFICES ASSUME NEW x \in CMC, NEW y \in CTranExcl(x) PROVE y \in CMC  OBVIOUS
  <2>1. y \in CTran(x)  BY DEF CTranExcl
  <2> QED BY <2>1, CTranLevelLE DEF CTranBelowProp
<1>2. \A x \in CMC : \A y \in CTranExcl(x) : CMinLevel(y) < CMinLevel(x)
  BY CTranExclDecreasesLevel
<1>3. CRecursiveFunc(CCflR, CTranExcl, m) =
        CCflR(m, {CRecursiveFunc(CCflR, CTranExcl, p) : p \in CTranExcl(m)})
  BY <1>1, <1>2, CRecursiveFuncRec
<1> QED BY <1>3 DEF CCfl
=============================================================================
